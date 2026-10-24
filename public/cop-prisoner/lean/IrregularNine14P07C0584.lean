import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0334
import IrregularNine14P07C0335

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b35040 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 388 41 88 179 211 147 403), lower := (rows 35 70 388 41 88 32 64 128 256), losses := [] }

theorem u35040 : Upper (D 7) (R 7) [34,68,384,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35041 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 388 41 145 122 90 218 346), lower := (rows 35 70 388 41 145 32 64 128 256), losses := [] }

theorem u35041 : Upper (D 7) (R 7) [34,68,384,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35041 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35042 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 388 41 146 121 89 217 345), lower := (rows 35 70 388 41 146 32 64 128 256), losses := [] }

theorem u35042 : Upper (D 7) (R 7) [34,68,384,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35043 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 388 41 152 115 83 211 339), lower := (rows 35 70 388 41 152 32 64 128 256), losses := [] }

theorem u35043 : Upper (D 7) (R 7) [34,68,384,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35043 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35044 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 388 41 208 59 91 155 283), lower := (rows 35 70 388 41 208 32 64 128 256), losses := [] }

theorem u35044 : Upper (D 7) (R 7) [34,68,384,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35044 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35045 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 388 42 81 185 217 153 409), lower := (rows 35 70 388 42 81 32 64 128 256), losses := [] }

theorem u35045 : Upper (D 7) (R 7) [34,68,384,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35046 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 388 42 88 177 209 145 401), lower := (rows 35 70 388 42 88 32 64 128 256), losses := [] }

theorem u35046 : Upper (D 7) (R 7) [34,68,384,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35046 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35047 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 388 42 145 121 89 217 345), lower := (rows 35 70 388 42 145 32 64 128 256), losses := [] }

theorem u35047 : Upper (D 7) (R 7) [34,68,384,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35048 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 388 42 152 113 81 209 337), lower := (rows 35 70 388 42 152 32 64 128 256), losses := [] }

theorem u35048 : Upper (D 7) (R 7) [34,68,384,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35049 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 388 42 208 57 89 153 281), lower := (rows 35 70 388 42 208 32 64 128 256), losses := [] }

theorem u35049 : Upper (D 7) (R 7) [34,68,384,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35049 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35050 : Route 9 := (fun mask => (mask,id))

def c35050 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35050 : Upper (D 7) (R 7) [34,68,384,48,65] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48,65] 13 (by decide) (choices 1) [1,2,8,128] r35050 c35050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20086
  · exact u20087
  · exact u20088
  · exact u20089

def b35051 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 169, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 388 56 82 169 201 137 393), lower := (rows 35 70 388 56 82 32 64 128 256), losses := [] }

theorem u35051 : Upper (D 7) (R 7) [34,68,384,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35052 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(1,5),(2,5),(2,6)], upper := (rows 35 70 388 56 88 163 195 131 387), lower := (rows 35 70 388 56 88 32 64 128 256), losses := [] }

theorem u35052 : Upper (D 7) (R 7) [34,68,384,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35052 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35053 : Route 9 := (fun mask => (mask,id))

def c35053 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35053 : Upper (D 7) (R 7) [34,68,384,48,129] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48,129] 13 (by decide) (choices 1) [1,2,8,64] r35053 c35053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20090
  · exact u20091
  · exact u20092
  · exact u20093

def r35054 : Route 9 := (fun mask => (mask,id))

def c35054 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35054 : Upper (D 7) (R 7) [34,68,384,48,130] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48,130] 13 (by decide) (choices 1) [1,8,64] r35054 c35054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20094
  · exact u20095
  · exact u20096

def b35055 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(2,5)], upper := (rows 35 70 388 56 152 99 67 195 323), lower := (rows 35 70 388 56 152 32 64 128 256), losses := [] }

theorem u35055 : Upper (D 7) (R 7) [34,68,384,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35055 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35056 : Route 9 := (fun mask => (mask,id))

def c35056 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35056 : Upper (D 7) (R 7) [34,68,384,48,192] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48,192] 13 (by decide) (choices 1) [1,2,8] r35056 c35056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20097
  · exact u20098
  · exact u20099

def r35057 : Route 9 := (fun mask => (mask,id))

def c35057 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35057 : Upper (D 7) (R 7) [34,68,384,65,129] 13 := by
  apply FastRouting.sound _ _ [34,68,384,65,129] 13 (by decide) (choices 1) [2,8,16] r35057 c35057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20100
  · exact u20101
  · exact u20102

def r35058 : Route 9 := (fun mask => (mask,id))

def c35058 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35058 : Upper (D 7) (R 7) [34,68,384,65,130] 13 := by
  apply FastRouting.sound _ _ [34,68,384,65,130] 13 (by decide) (choices 1) [1,8,16] r35058 c35058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20103
  · exact u20104
  · exact u20105

def r35059 : Route 9 := (fun mask => (mask,id))

def c35059 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35059 : Upper (D 7) (R 7) [34,68,384,65,136] 13 := by
  apply FastRouting.sound _ _ [34,68,384,65,136] 13 (by decide) (choices 1) [1,2,16] r35059 c35059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20106
  · exact u20107
  · exact u20108

def r35060 : Route 9 := (fun mask => (mask,id))

def c35060 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35060 : Upper (D 7) (R 7) [34,68,384,65,160] 13 := by
  apply FastRouting.sound _ _ [34,68,384,65,160] 13 (by decide) (choices 1) [1,2,8,16] r35060 c35060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20109
  · exact u20110
  · exact u20111
  · exact u20112

def b35061 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 177, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 388 74 145 57 121 185 313), lower := (rows 35 70 388 74 145 32 64 128 256), losses := [] }

theorem u35061 : Upper (D 7) (R 7) [34,68,384,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35061 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35062 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 177, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 388 74 152 49 113 177 305), lower := (rows 35 70 388 74 152 32 64 128 256), losses := [] }

theorem u35062 : Upper (D 7) (R 7) [34,68,384,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35062 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35063 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 177, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 388 74 176 57 89 153 281), lower := (rows 35 70 388 74 176 32 64 128 256), losses := [] }

theorem u35063 : Upper (D 7) (R 7) [34,68,384,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35064 : Route 9 := (fun mask => (mask,id))

def c35064 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35064 : Upper (D 7) (R 7) [34,68,384,80,129] 13 := by
  apply FastRouting.sound _ _ [34,68,384,80,129] 13 (by decide) (choices 1) [1,2,8] r35064 c35064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20113
  · exact u20114
  · exact u20115

def r35065 : Route 9 := (fun mask => (mask,id))

def c35065 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35065 : Upper (D 7) (R 7) [34,68,384,80,130] 13 := by
  apply FastRouting.sound _ _ [34,68,384,80,130] 13 (by decide) (choices 1) [1,8] r35065 c35065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20116
  · exact u20117

def b35066 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(2,6)], upper := (rows 35 70 388 88 152 35 99 163 291), lower := (rows 35 70 388 88 152 32 64 128 256), losses := [] }

theorem u35066 : Upper (D 7) (R 7) [34,68,384,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35066 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35067 : Route 9 := (fun mask => (mask,id))

def c35067 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35067 : Upper (D 7) (R 7) [34,68,384,80,160] 13 := by
  apply FastRouting.sound _ _ [34,68,384,80,160] 13 (by decide) (choices 1) [1,2,8] r35067 c35067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20118
  · exact u20119
  · exact u20120

def r35068 : Route 9 := (fun mask => (mask,id))

def c35068 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35068 : Upper (D 7) (R 7) [34,68,384,96,129] 13 := by
  apply FastRouting.sound _ _ [34,68,384,96,129] 13 (by decide) (choices 1) [1,2,8,16] r35068 c35068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20121
  · exact u20122
  · exact u20123
  · exact u20124

def r35069 : Route 9 := (fun mask => (mask,id))

def c35069 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35069 : Upper (D 7) (R 7) [34,68,384,96,130] 13 := by
  apply FastRouting.sound _ _ [34,68,384,96,130] 13 (by decide) (choices 1) [1,8,16] r35069 c35069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20125
  · exact u20126
  · exact u20127

def r35070 : Route 9 := (fun mask => (mask,id))

def c35070 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35070 : Upper (D 7) (R 7) [34,68,384,96,136] 13 := by
  apply FastRouting.sound _ _ [34,68,384,96,136] 13 (by decide) (choices 1) [1,2,16] r35070 c35070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20128
  · exact u20129
  · exact u20130

def b35071 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 7 13 56 496 464 464 464), lower := (rows 35 194 7 13 56 32 64 128 256), losses := [] }

theorem u35071 : Upper (D 7) (R 7) [34,192,3,5,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35072 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 194 7 13 88 432 496 432 432), lower := (rows 35 194 7 13 88 32 64 128 256), losses := [] }

theorem u35072 : Upper (D 7) (R 7) [34,192,3,5,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35073 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 194 7 13 112 440 472 408 408), lower := (rows 35 194 7 13 112 32 64 128 256), losses := [] }

theorem u35073 : Upper (D 7) (R 7) [34,192,3,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35073 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35074 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 194 7 13 280 240 240 240 496), lower := (rows 35 194 7 13 280 32 64 128 256), losses := [] }

theorem u35074 : Upper (D 7) (R 7) [34,192,3,5,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35074 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35075 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 194 7 13 304 248 216 216 472), lower := (rows 35 194 7 13 304 32 64 128 256), losses := [] }

theorem u35075 : Upper (D 7) (R 7) [34,192,3,5,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35076 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 194 7 13 336 184 248 184 440), lower := (rows 35 194 7 13 336 32 64 128 256), losses := [] }

theorem u35076 : Upper (D 7) (R 7) [34,192,3,5,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35077 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 28, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 194 7 25 28 480 480 480 480), lower := (rows 35 194 7 25 28 32 64 128 256), losses := [] }

theorem u35077 : Upper (D 7) (R 7) [34,192,3,17,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35077 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35078 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 7 25 52 488 456 456 456), lower := (rows 35 194 7 25 52 32 64 128 256), losses := [] }

theorem u35078 : Upper (D 7) (R 7) [34,192,3,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35079 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 25 84 424 488 424 424), lower := (rows 35 194 7 25 84 32 64 128 256), losses := [] }

theorem u35079 : Upper (D 7) (R 7) [34,192,3,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35079 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35080 : PairBound 9 := { available := 420, camps := [{ cop := 0, region := 4, targets := 160 },{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6),(2,5),(2,6),(2,7)], upper := (rows 35 194 7 25 88 420 484 420 420), lower := (rows 35 194 7 25 88 32 64 128 256), losses := [] }

theorem u35080 : Upper (D 7) (R 7) [34,192,3,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35081 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 25 112 428 460 396 396), lower := (rows 35 194 7 25 112 32 64 128 256), losses := [] }

theorem u35081 : Upper (D 7) (R 7) [34,192,3,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35081 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35082 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 25 276 232 232 232 488), lower := (rows 35 194 7 25 276 32 64 128 256), losses := [] }

theorem u35082 : Upper (D 7) (R 7) [34,192,3,17,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35082 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35083 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 25 280 228 228 228 484), lower := (rows 35 194 7 25 280 32 64 128 256), losses := [] }

theorem u35083 : Upper (D 7) (R 7) [34,192,3,17,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35084 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 25 304 236 204 204 460), lower := (rows 35 194 7 25 304 32 64 128 256), losses := [] }

theorem u35084 : Upper (D 7) (R 7) [34,192,3,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35084 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35085 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 25 336 172 236 172 428), lower := (rows 35 194 7 25 336 32 64 128 256), losses := [] }

theorem u35085 : Upper (D 7) (R 7) [34,192,3,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35085 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35086 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 7 28 56 481 449 449 449), lower := (rows 35 194 7 28 56 32 64 128 256), losses := [] }

theorem u35086 : Upper (D 7) (R 7) [34,192,3,20,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35087 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 28 81 424 488 424 424), lower := (rows 35 194 7 28 81 32 64 128 256), losses := [] }

theorem u35087 : Upper (D 7) (R 7) [34,192,3,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35088 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 4, targets := 160 },{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6),(2,5),(2,6),(2,7)], upper := (rows 35 194 7 28 88 417 481 417 417), lower := (rows 35 194 7 28 88 32 64 128 256), losses := [] }

theorem u35088 : Upper (D 7) (R 7) [34,192,3,20,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35089 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 28 112 425 457 393 393), lower := (rows 35 194 7 28 112 32 64 128 256), losses := [] }

theorem u35089 : Upper (D 7) (R 7) [34,192,3,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35089 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35090 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 28 273 232 232 232 488), lower := (rows 35 194 7 28 273 32 64 128 256), losses := [] }

theorem u35090 : Upper (D 7) (R 7) [34,192,3,20,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35090 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35091 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 28 280 225 225 225 481), lower := (rows 35 194 7 28 280 32 64 128 256), losses := [] }

theorem u35091 : Upper (D 7) (R 7) [34,192,3,20,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35092 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 28 304 233 201 201 457), lower := (rows 35 194 7 28 304 32 64 128 256), losses := [] }

theorem u35092 : Upper (D 7) (R 7) [34,192,3,20,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35092 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35093 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 28 336 169 233 169 425), lower := (rows 35 194 7 28 336 32 64 128 256), losses := [] }

theorem u35093 : Upper (D 7) (R 7) [34,192,3,20,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35094 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 7 44 81 440 472 408 408), lower := (rows 35 194 7 44 81 32 64 128 256), losses := [] }

theorem u35094 : Upper (D 7) (R 7) [34,192,3,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35094 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35095 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 7 44 88 433 465 401 401), lower := (rows 35 194 7 44 88 32 64 128 256), losses := [] }

theorem u35095 : Upper (D 7) (R 7) [34,192,3,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35096 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 7 44 273 248 216 216 472), lower := (rows 35 194 7 44 273 32 64 128 256), losses := [] }

theorem u35096 : Upper (D 7) (R 7) [34,192,3,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35096 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35097 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 7 44 280 241 209 209 465), lower := (rows 35 194 7 44 280 32 64 128 256), losses := [] }

theorem u35097 : Upper (D 7) (R 7) [34,192,3,36,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35098 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 7 44 336 185 217 153 409), lower := (rows 35 194 7 44 336 32 64 128 256), losses := [] }

theorem u35098 : Upper (D 7) (R 7) [34,192,3,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35099 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 56 81 428 460 396 396), lower := (rows 35 194 7 56 81 32 64 128 256), losses := [] }

theorem u35099 : Upper (D 7) (R 7) [34,192,3,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35099 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u35099
end Delivery.IrregularNine14.P07
