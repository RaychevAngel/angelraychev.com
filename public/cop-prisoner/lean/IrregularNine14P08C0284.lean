import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0103
import IrregularNine14P08C0104

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17040 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 194 44 104 176 53 85 149 277), lower := (rows 259 194 44 104 176 32 64 128 256), losses := [] }

theorem u17040 : Upper (D 8) (R 8) [258,192,40,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17040 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17041 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 7 56 88 224 224 224 480), lower := (rows 289 7 7 56 88 32 64 128 256), losses := [] }

theorem u17041 : Upper (D 8) (R 8) [288,5,3,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17041 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17042 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 7 56 208 232 232 232 488), lower := (rows 289 7 7 56 208 32 64 128 256), losses := [] }

theorem u17042 : Upper (D 8) (R 8) [288,5,3,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17042 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17043 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 7 88 152 224 224 224 480), lower := (rows 289 7 7 88 152 32 64 128 256), losses := [] }

theorem u17043 : Upper (D 8) (R 8) [288,5,3,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17043 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17044 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 7 88 176 232 232 232 488), lower := (rows 289 7 7 88 176 32 64 128 256), losses := [] }

theorem u17044 : Upper (D 8) (R 8) [288,5,3,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17044 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17045 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 7 104 176 248 216 216 472), lower := (rows 289 7 7 104 176 32 64 128 256), losses := [] }

theorem u17045 : Upper (D 8) (R 8) [288,5,3,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17045 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17046 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 7 104 208 184 248 184 440), lower := (rows 289 7 7 104 208 32 64 128 256), losses := [] }

theorem u17046 : Upper (D 8) (R 8) [288,5,3,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17046 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17047 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 26 112 224 224 224 480), lower := (rows 289 7 13 26 112 32 64 128 256), losses := [] }

theorem u17047 : Upper (D 8) (R 8) [288,5,9,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17047 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17048 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 26 208 224 224 224 480), lower := (rows 289 7 13 26 208 32 64 128 256), losses := [] }

theorem u17048 : Upper (D 8) (R 8) [288,5,9,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17048 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17049 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 13 42 112 240 208 208 464), lower := (rows 289 7 13 42 112 32 64 128 256), losses := [] }

theorem u17049 : Upper (D 8) (R 8) [288,5,9,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17049 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17050 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 13 42 208 240 240 240 496), lower := (rows 289 7 13 42 208 32 64 128 256), losses := [] }

theorem u17050 : Upper (D 8) (R 8) [288,5,9,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17050 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17051 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 56 82 224 224 224 480), lower := (rows 289 7 13 56 82 32 64 128 256), losses := [] }

theorem u17051 : Upper (D 8) (R 8) [288,5,9,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17051 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17052 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 56 208 226 226 226 482), lower := (rows 289 7 13 56 208 32 64 128 256), losses := [] }

theorem u17052 : Upper (D 8) (R 8) [288,5,9,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17052 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17053 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 74 112 176 240 176 432), lower := (rows 289 7 13 74 112 32 64 128 256), losses := [] }

theorem u17053 : Upper (D 8) (R 8) [288,5,9,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17053 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17054 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 74 176 240 240 240 496), lower := (rows 289 7 13 74 176 32 64 128 256), losses := [] }

theorem u17054 : Upper (D 8) (R 8) [288,5,9,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17054 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17055 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 74 208 176 240 176 432), lower := (rows 289 7 13 74 208 32 64 128 256), losses := [] }

theorem u17055 : Upper (D 8) (R 8) [288,5,9,66,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17055 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17056 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 88 50 224 224 224 480), lower := (rows 289 7 13 88 50 32 64 128 256), losses := [] }

theorem u17056 : Upper (D 8) (R 8) [288,5,9,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17056 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17057 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 88 146 224 224 224 480), lower := (rows 289 7 13 88 146 32 64 128 256), losses := [] }

theorem u17057 : Upper (D 8) (R 8) [288,5,9,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17057 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17058 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 88 176 226 226 226 482), lower := (rows 289 7 13 88 176 32 64 128 256), losses := [] }

theorem u17058 : Upper (D 8) (R 8) [288,5,9,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17058 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17059 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 104 50 240 208 208 464), lower := (rows 289 7 13 104 50 32 64 128 256), losses := [] }

theorem u17059 : Upper (D 8) (R 8) [288,5,9,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17059 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17060 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 104 82 176 240 176 432), lower := (rows 289 7 13 104 82 32 64 128 256), losses := [] }

theorem u17060 : Upper (D 8) (R 8) [288,5,9,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17060 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17061 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 104 146 240 240 240 496), lower := (rows 289 7 13 104 146 32 64 128 256), losses := [] }

theorem u17061 : Upper (D 8) (R 8) [288,5,9,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17061 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17062 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 104 176 242 210 210 466), lower := (rows 289 7 13 104 176 32 64 128 256), losses := [] }

theorem u17062 : Upper (D 8) (R 8) [288,5,9,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17062 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17063 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 104 208 178 242 178 434), lower := (rows 289 7 13 104 208 32 64 128 256), losses := [] }

theorem u17063 : Upper (D 8) (R 8) [288,5,9,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17063 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17064 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 200 50 240 240 240 496), lower := (rows 289 7 13 200 50 32 64 128 256), losses := [] }

theorem u17064 : Upper (D 8) (R 8) [288,5,9,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17064 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17065 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 200 82 176 240 176 432), lower := (rows 289 7 13 200 82 32 64 128 256), losses := [] }

theorem u17065 : Upper (D 8) (R 8) [288,5,9,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17065 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17066 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 200 112 178 242 178 434), lower := (rows 289 7 13 200 112 32 64 128 256), losses := [] }

theorem u17066 : Upper (D 8) (R 8) [288,5,9,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17066 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17067 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 14 25 112 224 224 224 480), lower := (rows 289 7 14 25 112 32 64 128 256), losses := [] }

theorem u17067 : Upper (D 8) (R 8) [288,5,10,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17067 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17068 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 14 25 208 224 224 224 480), lower := (rows 289 7 14 25 208 32 64 128 256), losses := [] }

theorem u17068 : Upper (D 8) (R 8) [288,5,10,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17068 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17069 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 14 41 112 240 208 208 464), lower := (rows 289 7 14 41 112 32 64 128 256), losses := [] }

theorem u17069 : Upper (D 8) (R 8) [288,5,10,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17069 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17070 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 14 41 208 240 240 240 496), lower := (rows 289 7 14 41 208 32 64 128 256), losses := [] }

theorem u17070 : Upper (D 8) (R 8) [288,5,10,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17070 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17071 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 30, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 14 56 49 224 192 192 448), lower := (rows 289 7 14 56 49 32 64 128 256), losses := [] }

theorem u17071 : Upper (D 8) (R 8) [288,5,10,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17071 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17072 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 168, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 14 56 81 224 224 224 480), lower := (rows 289 7 14 56 81 32 64 128 256), losses := [] }

theorem u17072 : Upper (D 8) (R 8) [288,5,10,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17072 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17073 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 14 56 112 225 193 193 449), lower := (rows 289 7 14 56 112 32 64 128 256), losses := [] }

theorem u17073 : Upper (D 8) (R 8) [288,5,10,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17073 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17074 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c17074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17074 : Upper (D 8) (R 8) [288,5,10,48,192] 13 := by
  apply FastRouting.sound _ _ [288,5,10,48,192] 13 (by decide) (choices 1) [1,64] r17074 c17074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6231
  · exact u6232

def b17075 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 14 73 112 176 240 176 432), lower := (rows 289 7 14 73 112 32 64 128 256), losses := [] }

theorem u17075 : Upper (D 8) (R 8) [288,5,10,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17075 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17076 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 14 73 176 240 240 240 496), lower := (rows 289 7 14 73 176 32 64 128 256), losses := [] }

theorem u17076 : Upper (D 8) (R 8) [288,5,10,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17076 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17077 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 14 73 208 176 240 176 432), lower := (rows 289 7 14 73 208 32 64 128 256), losses := [] }

theorem u17077 : Upper (D 8) (R 8) [288,5,10,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17077 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17078 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 289 7 14 88 49 224 224 224 480), lower := (rows 289 7 14 88 49 32 64 128 256), losses := [] }

theorem u17078 : Upper (D 8) (R 8) [288,5,10,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17078 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17079 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 14 88 81 160 224 160 416), lower := (rows 289 7 14 88 81 32 64 128 256), losses := [] }

theorem u17079 : Upper (D 8) (R 8) [288,5,10,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17079 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17080 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 14 88 112 161 225 161 417), lower := (rows 289 7 14 88 112 32 64 128 256), losses := [] }

theorem u17080 : Upper (D 8) (R 8) [288,5,10,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17080 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17081 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 14 88 145 224 224 224 480), lower := (rows 289 7 14 88 145 32 64 128 256), losses := [] }

theorem u17081 : Upper (D 8) (R 8) [288,5,10,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17081 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17082 : Route 9 := (fun mask => (mask,id))

def c17082 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17082 : Upper (D 8) (R 8) [288,5,10,80,160] 13 := by
  apply FastRouting.sound _ _ [288,5,10,80,160] 13 (by decide) (choices 1) [1,64,128] r17082 c17082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6233
  · exact u6234
  · exact u6235

def b17083 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 14 88 208 161 225 161 417), lower := (rows 289 7 14 88 208 32 64 128 256), losses := [] }

theorem u17083 : Upper (D 8) (R 8) [288,5,10,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17083 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17084 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 289 7 14 104 49 240 208 208 464), lower := (rows 289 7 14 104 49 32 64 128 256), losses := [] }

theorem u17084 : Upper (D 8) (R 8) [288,5,10,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17084 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17085 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 168, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 14 104 81 176 240 176 432), lower := (rows 289 7 14 104 81 32 64 128 256), losses := [] }

theorem u17085 : Upper (D 8) (R 8) [288,5,10,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17085 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17086 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 14 104 112 177 209 145 401), lower := (rows 289 7 14 104 112 32 64 128 256), losses := [] }

theorem u17086 : Upper (D 8) (R 8) [288,5,10,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17086 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17087 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 14 104 145 240 240 240 496), lower := (rows 289 7 14 104 145 32 64 128 256), losses := [] }

theorem u17087 : Upper (D 8) (R 8) [288,5,10,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17087 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17088 : Route 9 := (fun mask => (mask,id))

def c17088 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u17088 : Upper (D 8) (R 8) [288,5,10,96,160] 13 := by
  apply FastRouting.sound _ _ [288,5,10,96,160] 13 (by decide) (choices 1) [1,16,64,128] r17088 c17088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6236
  · exact u6237
  · exact u6238
  · exact u6239

def b17089 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 14 104 208 177 241 177 433), lower := (rows 289 7 14 104 208 32 64 128 256), losses := [] }

theorem u17089 : Upper (D 8) (R 8) [288,5,10,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17089 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17090 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 289 7 14 200 49 240 240 240 496), lower := (rows 289 7 14 200 49 32 64 128 256), losses := [] }

theorem u17090 : Upper (D 8) (R 8) [288,5,10,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17090 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17091 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 168, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 14 200 81 176 240 176 432), lower := (rows 289 7 14 200 81 32 64 128 256), losses := [] }

theorem u17091 : Upper (D 8) (R 8) [288,5,10,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17091 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17092 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 14 200 112 177 241 177 433), lower := (rows 289 7 14 200 112 32 64 128 256), losses := [] }

theorem u17092 : Upper (D 8) (R 8) [288,5,10,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17092 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17093 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 14 200 208 49 113 177 305), lower := (rows 289 7 14 200 208 32 64 128 256), losses := [] }

theorem u17093 : Upper (D 8) (R 8) [288,5,10,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17093 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17094 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 30, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 28 41 50 224 192 192 448), lower := (rows 289 7 28 41 50 32 64 128 256), losses := [] }

theorem u17094 : Upper (D 8) (R 8) [288,5,24,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17094 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17095 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 28 41 82 224 224 224 480), lower := (rows 289 7 28 41 82 32 64 128 256), losses := [] }

theorem u17095 : Upper (D 8) (R 8) [288,5,24,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17095 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17096 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 28 41 112 226 194 194 450), lower := (rows 289 7 28 41 112 32 64 128 256), losses := [] }

theorem u17096 : Upper (D 8) (R 8) [288,5,24,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17096 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17097 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 28 41 208 226 226 226 482), lower := (rows 289 7 28 41 208 32 64 128 256), losses := [] }

theorem u17097 : Upper (D 8) (R 8) [288,5,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17097 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17098 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 28 42 81 224 224 224 480), lower := (rows 289 7 28 42 81 32 64 128 256), losses := [] }

theorem u17098 : Upper (D 8) (R 8) [288,5,24,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17098 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17099 : Route 9 := (fun mask => (mask,id))

def c17099 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17099 : Upper (D 8) (R 8) [288,5,24,34,96] 13 := by
  apply FastRouting.sound _ _ [288,5,24,34,96] 13 (by decide) (choices 1) [1,64,128] r17099 c17099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6240
  · exact u6241
  · exact u6242

#print axioms u17099
end Delivery.IrregularNine14.P08
