import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0096

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16080 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 44 88 112 161 225 161 417), lower := (rows 259 7 44 88 112 32 64 128 256), losses := [] }

theorem u16080 : Upper (D 8) (R 8) [258,5,40,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16080 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16081 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 44 88 145 224 224 224 480), lower := (rows 259 7 44 88 145 32 64 128 256), losses := [] }

theorem u16081 : Upper (D 8) (R 8) [258,5,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16081 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16082 : Route 9 := (fun mask => (mask,id))

def c16082 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16082 : Upper (D 8) (R 8) [258,5,40,80,160] 13 := by
  apply FastRouting.sound _ _ [258,5,40,80,160] 13 (by decide) (choices 1) [1,64,128] r16082 c16082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5777
  · exact u5778
  · exact u5779

def b16083 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 44 88 208 161 225 161 417), lower := (rows 259 7 44 88 208 32 64 128 256), losses := [] }

theorem u16083 : Upper (D 8) (R 8) [258,5,40,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16083 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16084 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 204, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 44 200 49 240 240 240 496), lower := (rows 259 7 44 200 49 32 64 128 256), losses := [] }

theorem u16084 : Upper (D 8) (R 8) [258,5,40,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16084 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16085 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 172, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 44 200 81 176 240 176 432), lower := (rows 259 7 44 200 81 32 64 128 256), losses := [] }

theorem u16085 : Upper (D 8) (R 8) [258,5,40,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16085 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16086 : Route 9 := (fun mask => (mask,id))

def c16086 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16086 : Upper (D 8) (R 8) [258,5,40,192,96] 13 := by
  apply FastRouting.sound _ _ [258,5,40,192,96] 13 (by decide) (choices 1) [1,16,128] r16086 c16086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5780
  · exact u5781
  · exact u5782

def b16087 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 7 44 200 208 49 113 177 305), lower := (rows 259 7 44 200 208 32 64 128 256), losses := [] }

theorem u16087 : Upper (D 8) (R 8) [258,5,40,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16087 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16088 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 204, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 76 56 49 224 224 224 480), lower := (rows 259 7 76 56 49 32 64 128 256), losses := [] }

theorem u16088 : Upper (D 8) (R 8) [258,5,72,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16088 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16089 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 76 56 81 160 224 160 416), lower := (rows 259 7 76 56 81 32 64 128 256), losses := [] }

theorem u16089 : Upper (D 8) (R 8) [258,5,72,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16089 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16090 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 76 56 112 161 225 161 417), lower := (rows 259 7 76 56 112 32 64 128 256), losses := [] }

theorem u16090 : Upper (D 8) (R 8) [258,5,72,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16090 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16091 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 76 56 145 224 224 224 480), lower := (rows 259 7 76 56 145 32 64 128 256), losses := [] }

theorem u16091 : Upper (D 8) (R 8) [258,5,72,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16091 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16092 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 7 76 56 176 225 225 225 481), lower := (rows 259 7 76 56 176 32 64 128 256), losses := [] }

theorem u16092 : Upper (D 8) (R 8) [258,5,72,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16092 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16093 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 76 56 208 161 225 161 417), lower := (rows 259 7 76 56 208 32 64 128 256), losses := [] }

theorem u16093 : Upper (D 8) (R 8) [258,5,72,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16093 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16094 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 204, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 76 152 49 224 224 224 480), lower := (rows 259 7 76 152 49 32 64 128 256), losses := [] }

theorem u16094 : Upper (D 8) (R 8) [258,5,72,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16094 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16095 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 76 152 81 160 224 160 416), lower := (rows 259 7 76 152 81 32 64 128 256), losses := [] }

theorem u16095 : Upper (D 8) (R 8) [258,5,72,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16095 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16096 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 76 152 112 161 225 161 417), lower := (rows 259 7 76 152 112 32 64 128 256), losses := [] }

theorem u16096 : Upper (D 8) (R 8) [258,5,72,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16096 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16097 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 76 152 145 96 96 224 352), lower := (rows 259 7 76 152 145 32 64 128 256), losses := [] }

theorem u16097 : Upper (D 8) (R 8) [258,5,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16097 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16098 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 76 152 176 97 97 225 353), lower := (rows 259 7 76 152 176 32 64 128 256), losses := [] }

theorem u16098 : Upper (D 8) (R 8) [258,5,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16098 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16099 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 76 152 208 33 97 161 289), lower := (rows 259 7 76 152 208 32 64 128 256), losses := [] }

theorem u16099 : Upper (D 8) (R 8) [258,5,72,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16099 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16100 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 204, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 76 168 49 240 240 240 496), lower := (rows 259 7 76 168 49 32 64 128 256), losses := [] }

theorem u16100 : Upper (D 8) (R 8) [258,5,72,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16100 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16101 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 172, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 76 168 81 176 240 176 432), lower := (rows 259 7 76 168 81 32 64 128 256), losses := [] }

theorem u16101 : Upper (D 8) (R 8) [258,5,72,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16101 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16102 : Route 9 := (fun mask => (mask,id))

def c16102 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16102 : Upper (D 8) (R 8) [258,5,72,160,96] 13 := by
  apply FastRouting.sound _ _ [258,5,72,160,96] 13 (by decide) (choices 1) [1,16,128] r16102 c16102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5783
  · exact u5784
  · exact u5785

def b16103 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 76 168 145 112 112 240 368), lower := (rows 259 7 76 168 145 32 64 128 256), losses := [] }

theorem u16103 : Upper (D 8) (R 8) [258,5,72,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16103 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16104 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 7 76 168 176 113 113 241 369), lower := (rows 259 7 76 168 176 32 64 128 256), losses := [] }

theorem u16104 : Upper (D 8) (R 8) [258,5,72,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16104 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16105 : Route 9 := (fun mask => (mask,id))

def c16105 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16105 : Upper (D 8) (R 8) [258,5,72,160,192] 13 := by
  apply FastRouting.sound _ _ [258,5,72,160,192] 13 (by decide) (choices 1) [1,16] r16105 c16105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5786
  · exact u5787

def b16106 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 25 56 224 224 224 480), lower := (rows 259 7 100 25 56 32 64 128 256), losses := [] }

theorem u16106 : Upper (D 8) (R 8) [258,5,96,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16106 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16107 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 100 25 88 160 224 160 416), lower := (rows 259 7 100 25 88 32 64 128 256), losses := [] }

theorem u16107 : Upper (D 8) (R 8) [258,5,96,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16107 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16108 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 25 152 224 224 224 480), lower := (rows 259 7 100 25 152 32 64 128 256), losses := [] }

theorem u16108 : Upper (D 8) (R 8) [258,5,96,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16108 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16109 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 25 176 232 232 232 488), lower := (rows 259 7 100 25 176 32 64 128 256), losses := [] }

theorem u16109 : Upper (D 8) (R 8) [258,5,96,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16109 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16110 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 25 208 168 232 168 424), lower := (rows 259 7 100 25 208 32 64 128 256), losses := [] }

theorem u16110 : Upper (D 8) (R 8) [258,5,96,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16110 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16111 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 41 56 240 208 208 464), lower := (rows 259 7 100 41 56 32 64 128 256), losses := [] }

theorem u16111 : Upper (D 8) (R 8) [258,5,96,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16111 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16112 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 41 88 176 240 176 432), lower := (rows 259 7 100 41 88 32 64 128 256), losses := [] }

theorem u16112 : Upper (D 8) (R 8) [258,5,96,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16112 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16113 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 41 152 240 240 240 496), lower := (rows 259 7 100 41 152 32 64 128 256), losses := [] }

theorem u16113 : Upper (D 8) (R 8) [258,5,96,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16113 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16114 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 41 176 248 216 216 472), lower := (rows 259 7 100 41 176 32 64 128 256), losses := [] }

theorem u16114 : Upper (D 8) (R 8) [258,5,96,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16114 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16115 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 41 208 184 248 184 440), lower := (rows 259 7 100 41 208 32 64 128 256), losses := [] }

theorem u16115 : Upper (D 8) (R 8) [258,5,96,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16115 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16116 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 7 100 56 56 225 193 193 449), lower := (rows 259 7 100 56 56 32 64 128 256), losses := [] }

theorem u16116 : Upper (D 8) (R 8) [258,5,96,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16116 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16117 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 172, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 56 81 168 232 168 424), lower := (rows 259 7 100 56 81 32 64 128 256), losses := [] }

theorem u16117 : Upper (D 8) (R 8) [258,5,96,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16117 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16118 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 7 100 56 88 161 225 161 417), lower := (rows 259 7 100 56 88 32 64 128 256), losses := [] }

theorem u16118 : Upper (D 8) (R 8) [258,5,96,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16118 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16119 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 7 100 56 112 169 201 137 393), lower := (rows 259 7 100 56 112 32 64 128 256), losses := [] }

theorem u16119 : Upper (D 8) (R 8) [258,5,96,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16119 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16120 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 56 145 232 232 232 488), lower := (rows 259 7 100 56 145 32 64 128 256), losses := [] }

theorem u16120 : Upper (D 8) (R 8) [258,5,96,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16120 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16121 : Route 9 := (fun mask => (mask,id))

def c16121 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16121 : Upper (D 8) (R 8) [258,5,96,48,136] 13 := by
  apply FastRouting.sound _ _ [258,5,96,48,136] 13 (by decide) (choices 1) [1,64,128] r16121 c16121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5788
  · exact u5789
  · exact u5790

def b16122 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 7 100 56 176 233 201 201 457), lower := (rows 259 7 100 56 176 32 64 128 256), losses := [] }

theorem u16122 : Upper (D 8) (R 8) [258,5,96,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16122 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16123 : Route 9 := (fun mask => (mask,id))

def c16123 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16123 : Upper (D 8) (R 8) [258,5,96,48,192] 13 := by
  apply FastRouting.sound _ _ [258,5,96,48,192] 13 (by decide) (choices 1) [1,8,128] r16123 c16123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5791
  · exact u5792
  · exact u5793

def b16124 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 73 152 176 240 176 432), lower := (rows 259 7 100 73 152 32 64 128 256), losses := [] }

theorem u16124 : Upper (D 8) (R 8) [258,5,96,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16124 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16125 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 73 176 184 248 184 440), lower := (rows 259 7 100 73 176 32 64 128 256), losses := [] }

theorem u16125 : Upper (D 8) (R 8) [258,5,96,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16125 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16126 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 88 145 168 232 168 424), lower := (rows 259 7 100 88 145 32 64 128 256), losses := [] }

theorem u16126 : Upper (D 8) (R 8) [258,5,96,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16126 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16127 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 100 88 152 161 225 161 417), lower := (rows 259 7 100 88 152 32 64 128 256), losses := [] }

theorem u16127 : Upper (D 8) (R 8) [258,5,96,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16127 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16128 : Route 9 := (fun mask => (mask,id))

def c16128 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16128 : Upper (D 8) (R 8) [258,5,96,80,160] 13 := by
  apply FastRouting.sound _ _ [258,5,96,80,160] 13 (by decide) (choices 1) [1,8,128] r16128 c16128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5794
  · exact u5795
  · exact u5796

def b16129 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 7 100 104 152 177 241 177 433), lower := (rows 259 7 100 104 152 32 64 128 256), losses := [] }

theorem u16129 : Upper (D 8) (R 8) [258,5,96,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16129 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16130 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 7 100 104 176 185 217 153 409), lower := (rows 259 7 100 104 176 32 64 128 256), losses := [] }

theorem u16130 : Upper (D 8) (R 8) [258,5,96,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16130 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16131 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 100 137 152 112 112 240 368), lower := (rows 259 7 100 137 152 32 64 128 256), losses := [] }

theorem u16131 : Upper (D 8) (R 8) [258,5,96,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16131 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16132 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 137 176 120 120 248 376), lower := (rows 259 7 100 137 176 32 64 128 256), losses := [] }

theorem u16132 : Upper (D 8) (R 8) [258,5,96,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16132 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16133 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 137 208 56 120 184 312), lower := (rows 259 7 100 137 208 32 64 128 256), losses := [] }

theorem u16133 : Upper (D 8) (R 8) [258,5,96,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16133 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16134 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 7 100 152 152 97 97 225 353), lower := (rows 259 7 100 152 152 32 64 128 256), losses := [] }

theorem u16134 : Upper (D 8) (R 8) [258,5,96,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16134 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16135 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 100 152 176 105 105 233 361), lower := (rows 259 7 100 152 176 32 64 128 256), losses := [] }

theorem u16135 : Upper (D 8) (R 8) [258,5,96,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16135 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16136 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 100 152 208 41 105 169 297), lower := (rows 259 7 100 152 208 32 64 128 256), losses := [] }

theorem u16136 : Upper (D 8) (R 8) [258,5,96,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16136 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16137 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 7 100 168 176 121 89 217 345), lower := (rows 259 7 100 168 176 32 64 128 256), losses := [] }

theorem u16137 : Upper (D 8) (R 8) [258,5,96,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16137 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16138 : Route 9 := (fun mask => (mask,id))

def c16138 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16138 : Upper (D 8) (R 8) [258,5,96,160,192] 13 := by
  apply FastRouting.sound _ _ [258,5,96,160,192] 13 (by decide) (choices 1) [1,8,16] r16138 c16138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5797
  · exact u5798
  · exact u5799

def b16139 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 196 25 56 224 224 224 480), lower := (rows 259 7 196 25 56 32 64 128 256), losses := [] }

theorem u16139 : Upper (D 8) (R 8) [258,5,192,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16139 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u16139
end Delivery.IrregularNine14.P08
