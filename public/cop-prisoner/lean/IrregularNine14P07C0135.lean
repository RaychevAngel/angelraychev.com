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

def b8100 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 37 98 196 152 273 34 72 131 259), lower := (rows 37 98 196 152 273 34 72 128 256), losses := [] }

theorem u8100 : Upper (D 7) (R 7) [36,96,192,144,257,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8100 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8101 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 1, region := 132, targets := 1 }], pairs := [(1,7),(2,0),(4,7)], upper := (rows 37 98 196 152 273 40 65 130 258), lower := (rows 37 98 196 152 273 40 65 128 256), losses := [] }

theorem u8101 : Upper (D 7) (R 7) [36,96,192,144,257,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8101 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8102 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0),(1,7),(4,7)], upper := (rows 37 98 196 152 273 40 66 131 259), lower := (rows 37 98 196 152 273 40 66 128 256), losses := [] }

theorem u8102 : Upper (D 7) (R 7) [36,96,192,144,257,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8102 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8103 : Route 9 := (fun mask => (mask,id))

def c8103 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8103 : Upper (D 7) (R 7) [36,96,192,144,258,2,1] 13 := by
  apply FastRouting.sound _ _ [36,96,192,144,258,2,1] 13 (by decide) (choices 1) [1,8] r8103 c8103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u644
  · exact u645

def b8104 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 37 98 196 152 274 34 72 129 257), lower := (rows 37 98 196 152 274 34 72 128 256), losses := [] }

theorem u8104 : Upper (D 7) (R 7) [36,96,192,144,258,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8104 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8105 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 3, region := 101, targets := 2 }], pairs := [(0,1),(1,7),(4,7)], upper := (rows 37 98 196 152 274 40 65 131 259), lower := (rows 37 98 196 152 274 40 65 128 256), losses := [] }

theorem u8105 : Upper (D 7) (R 7) [36,96,192,144,258,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8105 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8106 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 1, region := 133, targets := 2 }], pairs := [(0,1),(1,7),(4,7)], upper := (rows 37 98 196 152 274 40 66 129 257), lower := (rows 37 98 196 152 274 40 66 128 256), losses := [] }

theorem u8106 : Upper (D 7) (R 7) [36,96,192,144,258,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8106 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8107 : Route 9 := (fun mask => (mask,id))

def c8107 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8107 : Upper (D 7) (R 7) [36,96,192,144,264,2,1] 13 := by
  apply FastRouting.sound _ _ [36,96,192,144,264,2,1] 13 (by decide) (choices 1) [1,2] r8107 c8107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u646
  · exact u647

def b8108 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 408, targets := 98 }], pairs := [(3,1),(3,5),(3,6),(4,1)], upper := (rows 37 98 196 152 280 34 66 129 257), lower := (rows 37 98 196 152 280 34 66 128 256), losses := [] }

theorem u8108 : Upper (D 7) (R 7) [36,96,192,144,264,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8109 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 90, targets := 128 },{ cop := 1, region := 389, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 261 25 26 160 66 192 448), lower := (rows 37 98 261 25 26 160 66 128 256), losses := [] }

theorem u8109 : Upper (D 7) (R 7) [36,96,257,17,10,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8110 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 261 25 26 160 192 194 322), lower := (rows 37 98 261 25 26 160 192 128 256), losses := [] }

theorem u8110 : Upper (D 7) (R 7) [36,96,257,17,10,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8111 : PairBound 9 := { available := 72, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,5),(4,0)], upper := (rows 37 98 261 25 146 160 66 200 328), lower := (rows 37 98 261 25 146 160 66 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 82 136 264), good := (rows 5 66 261 477 210 128 66 128 256) }] }

theorem u8111 : Upper (D 7) (R 7) [36,96,257,17,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8112 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 261, targets := 128 },{ cop := 3, region := 226, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 37 98 261 25 146 160 72 194 322), lower := (rows 37 98 261 25 146 160 72 128 256), losses := [] }

theorem u8112 : Upper (D 7) (R 7) [36,96,257,17,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8112 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8113 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 261 25 208 34 66 136 392), lower := (rows 37 98 261 25 208 34 66 128 256), losses := [] }

theorem u8113 : Upper (D 7) (R 7) [36,96,257,17,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8114 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 37 98 261 25 208 34 72 130 386), lower := (rows 37 98 261 25 208 34 72 128 256), losses := [] }

theorem u8114 : Upper (D 7) (R 7) [36,96,257,17,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8114 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8115 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 98 261 25 208 34 192 138 266), lower := (rows 37 98 261 25 208 34 192 128 256), losses := [] }

theorem u8115 : Upper (D 7) (R 7) [36,96,257,17,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8116 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(4,0)], upper := (rows 37 98 261 25 208 160 66 138 266), lower := (rows 37 98 261 25 208 160 66 128 256), losses := [{ target := 7, region := (rows 1 35 12 8 16 32 111 0 264), good := (rows 103 98 327 351 80 98 66 0 256) }] }

theorem u8116 : Upper (D 7) (R 7) [36,96,257,17,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8117 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 261, targets := 64 },{ cop := 1, region := 261, targets := 128 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 98 261 25 208 160 72 130 258), lower := (rows 37 98 261 25 208 160 72 128 256), losses := [] }

theorem u8117 : Upper (D 7) (R 7) [36,96,257,17,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8117 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8118 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 405, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 98 261 26 145 34 72 192 448), lower := (rows 37 98 261 26 145 34 72 128 256), losses := [] }

theorem u8118 : Upper (D 7) (R 7) [36,96,257,18,129,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8118 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8119 : Route 9 := (fun mask => (mask,id))

def c8119 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8119 : Upper (D 7) (R 7) [36,96,257,18,129,2,128] 13 := by
  apply FastRouting.sound _ _ [36,96,257,18,129,2,128] 13 (by decide) (choices 1) [8,64] r8119 c8119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u648
  · exact u649

def b8120 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 405, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 98 261 26 145 40 66 192 448), lower := (rows 37 98 261 26 145 40 66 128 256), losses := [] }

theorem u8120 : Upper (D 7) (R 7) [36,96,257,18,129,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8120 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8121 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 261, targets := 128 },{ cop := 4, region := 106, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 37 98 261 26 145 40 192 194 322), lower := (rows 37 98 261 26 145 40 192 128 256), losses := [] }

theorem u8121 : Upper (D 7) (R 7) [36,96,257,18,129,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8121 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8122 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 106, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 37 98 261 26 145 160 66 200 328), lower := (rows 37 98 261 26 145 160 66 128 256), losses := [{ target := 7, region := (rows 1 35 20 24 16 32 127 0 280), good := (rows 103 98 327 350 351 98 66 0 256) }] }

theorem u8122 : Upper (D 7) (R 7) [36,96,257,18,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8122 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8123 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 261, targets := 128 },{ cop := 4, region := 106, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 37 98 261 26 145 160 72 194 322), lower := (rows 37 98 261 26 145 160 72 128 256), losses := [] }

theorem u8123 : Upper (D 7) (R 7) [36,96,257,18,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8123 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8124 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 6, region := 162, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 261 26 152 160 65 194 322), lower := (rows 37 98 261 26 152 160 65 128 256), losses := [] }

theorem u8124 : Upper (D 7) (R 7) [36,96,257,18,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8124 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8125 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 90, targets := 1 },{ cop := 5, region := 327, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 37 98 261 26 152 160 66 193 321), lower := (rows 37 98 261 26 152 160 66 128 256), losses := [] }

theorem u8125 : Upper (D 7) (R 7) [36,96,257,18,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8126 : PairBound 9 := { available := 144, camps := [{ cop := 8, region := 111, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 98 261 73 146 34 72 144 400), lower := (rows 37 98 261 73 146 34 72 128 256), losses := [] }

theorem u8126 : Upper (D 7) (R 7) [36,96,257,65,130,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8126 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8127 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 98 261 73 146 34 80 136 392), lower := (rows 37 98 261 73 146 34 80 128 256), losses := [] }

theorem u8127 : Upper (D 7) (R 7) [36,96,257,65,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8127 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8128 : Route 9 := (fun mask => (mask,id))

def c8128 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8128 : Upper (D 7) (R 7) [36,96,257,65,130,2,128] 13 := by
  apply FastRouting.sound _ _ [36,96,257,65,130,2,128] 13 (by decide) (choices 1) [8,16] r8128 c8128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u650
  · exact u651

def b8129 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 98 261 73 146 48 66 136 392), lower := (rows 37 98 261 73 146 48 66 128 256), losses := [] }

theorem u8129 : Upper (D 7) (R 7) [36,96,257,65,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8129 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8130 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 261 73 146 48 72 130 386), lower := (rows 37 98 261 73 146 48 72 128 256), losses := [] }

theorem u8130 : Upper (D 7) (R 7) [36,96,257,65,130,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8130 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8131 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 261 73 146 48 192 138 266), lower := (rows 37 98 261 73 146 48 192 128 256), losses := [] }

theorem u8131 : Upper (D 7) (R 7) [36,96,257,65,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8131 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8132 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 178, targets := 1 }], pairs := [(1,0),(1,7),(3,7),(4,0)], upper := (rows 37 98 261 73 146 160 66 152 280), lower := (rows 37 98 261 73 146 160 66 128 256), losses := [] }

theorem u8132 : Upper (D 7) (R 7) [36,96,257,65,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8133 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 261 73 146 160 72 146 274), lower := (rows 37 98 261 73 146 160 72 128 256), losses := [] }

theorem u8133 : Upper (D 7) (R 7) [36,96,257,65,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8133 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8134 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 261 73 146 160 80 138 266), lower := (rows 37 98 261 73 146 160 80 128 256), losses := [] }

theorem u8134 : Upper (D 7) (R 7) [36,96,257,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8134 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8135 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 404, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(4,1)], upper := (rows 37 98 261 73 152 34 66 144 400), lower := (rows 37 98 261 73 152 34 66 128 256), losses := [] }

theorem u8135 : Upper (D 7) (R 7) [36,96,257,65,136,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8136 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 37 98 261 73 152 34 80 130 386), lower := (rows 37 98 261 73 152 34 80 128 256), losses := [] }

theorem u8136 : Upper (D 7) (R 7) [36,96,257,65,136,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8136 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8137 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 178, targets := 1 },{ cop := 3, region := 34, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 37 98 261 73 152 34 192 146 274), lower := (rows 37 98 261 73 152 34 192 128 256), losses := [{ target := 7, region := (rows 17 74 20 8 16 122 64 0 272), good := (rows 37 98 261 107 319 34 98 0 256) }] }

theorem u8137 : Upper (D 7) (R 7) [36,96,257,65,136,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8138 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 178, targets := 1 }], pairs := [(1,0),(1,7),(3,7),(4,0)], upper := (rows 37 98 261 73 152 160 66 146 274), lower := (rows 37 98 261 73 152 160 66 128 256), losses := [] }

theorem u8138 : Upper (D 7) (R 7) [36,96,257,65,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8138 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8139 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 261 73 152 160 80 130 258), lower := (rows 37 98 261 73 152 160 80 128 256), losses := [] }

theorem u8139 : Upper (D 7) (R 7) [36,96,257,65,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8139 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8140 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 261 88 145 34 66 136 392), lower := (rows 37 98 261 88 145 34 66 128 256), losses := [] }

theorem u8140 : Upper (D 7) (R 7) [36,96,257,80,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8140 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8141 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 261 88 145 34 72 130 386), lower := (rows 37 98 261 88 145 34 72 128 256), losses := [] }

theorem u8141 : Upper (D 7) (R 7) [36,96,257,80,129,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8141 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8142 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 98, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 261 88 145 34 192 138 266), lower := (rows 37 98 261 88 145 34 192 128 256), losses := [] }

theorem u8142 : Upper (D 7) (R 7) [36,96,257,80,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8143 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 106, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 37 98 261 88 145 160 66 138 266), lower := (rows 37 98 261 88 145 160 66 128 256), losses := [{ target := 7, region := (rows 1 35 20 24 16 32 119 0 272), good := (rows 103 98 327 348 351 98 66 0 256) }] }

theorem u8143 : Upper (D 7) (R 7) [36,96,257,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8143 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8144 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 261 88 145 160 72 130 258), lower := (rows 37 98 261 88 145 160 72 128 256), losses := [] }

theorem u8144 : Upper (D 7) (R 7) [36,96,257,80,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8144 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8145 : PairBound 9 := { available := 10, camps := [{ cop := 6, region := 186, targets := 1 },{ cop := 1, region := 152, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 37 98 261 88 146 160 65 138 266), lower := (rows 37 98 261 88 146 160 65 128 256), losses := [] }

theorem u8145 : Upper (D 7) (R 7) [36,96,257,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8146 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 421, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 261 88 146 160 66 137 265), lower := (rows 37 98 261 88 146 160 66 128 256), losses := [] }

theorem u8146 : Upper (D 7) (R 7) [36,96,257,80,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8147 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 261 88 146 160 72 131 259), lower := (rows 37 98 261 88 146 160 72 128 256), losses := [] }

theorem u8147 : Upper (D 7) (R 7) [36,96,257,80,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8147 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8148 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 114, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 37 98 261 137 146 34 72 208 336), lower := (rows 37 98 261 137 146 34 72 128 256), losses := [] }

theorem u8148 : Upper (D 7) (R 7) [36,96,257,129,130,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8148 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8149 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 98 261 137 146 34 80 200 328), lower := (rows 37 98 261 137 146 34 80 128 256), losses := [] }

theorem u8149 : Upper (D 7) (R 7) [36,96,257,129,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8149 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8150 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 98 261 137 146 48 66 200 328), lower := (rows 37 98 261 137 146 48 66 128 256), losses := [] }

theorem u8150 : Upper (D 7) (R 7) [36,96,257,129,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8150 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8151 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 261, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 37 98 261 137 146 48 72 194 322), lower := (rows 37 98 261 137 146 48 72 128 256), losses := [] }

theorem u8151 : Upper (D 7) (R 7) [36,96,257,129,130,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8151 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8152 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 261 137 208 34 66 152 280), lower := (rows 37 98 261 137 208 34 66 128 256), losses := [] }

theorem u8152 : Upper (D 7) (R 7) [36,96,257,129,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8153 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 98 261 137 208 34 72 146 274), lower := (rows 37 98 261 137 208 34 72 128 256), losses := [] }

theorem u8153 : Upper (D 7) (R 7) [36,96,257,129,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8153 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8154 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 261 137 208 34 80 138 266), lower := (rows 37 98 261 137 208 34 80 128 256), losses := [] }

theorem u8154 : Upper (D 7) (R 7) [36,96,257,129,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8154 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8155 : PairBound 9 := { available := 24, camps := [{ cop := 6, region := 186, targets := 1 },{ cop := 8, region := 103, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 37 98 261 138 208 34 65 152 280), lower := (rows 37 98 261 138 208 34 65 128 256), losses := [] }

theorem u8155 : Upper (D 7) (R 7) [36,96,257,130,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8156 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 405, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 98 261 138 208 34 72 145 273), lower := (rows 37 98 261 138 208 34 72 128 256), losses := [] }

theorem u8156 : Upper (D 7) (R 7) [36,96,257,130,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8156 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8157 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 261 138 208 34 80 137 265), lower := (rows 37 98 261 138 208 34 80 128 256), losses := [] }

theorem u8157 : Upper (D 7) (R 7) [36,96,257,130,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8157 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8158 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 186, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 98 261 138 208 40 65 146 274), lower := (rows 37 98 261 138 208 40 65 128 256), losses := [] }

theorem u8158 : Upper (D 7) (R 7) [36,96,257,130,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8158 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8159 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 405, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 98 261 138 208 40 66 145 273), lower := (rows 37 98 261 138 208 40 66 128 256), losses := [] }

theorem u8159 : Upper (D 7) (R 7) [36,96,257,130,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8159 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u8159
end Delivery.IrregularNine14.P07
