import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0104

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r17100 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c17100 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17100 : Upper (D 8) (R 8) [288,5,24,34,192] 13 := by
  apply FastRouting.sound _ _ [288,5,24,34,192] 13 (by decide) (choices 1) [1,64] r17100 c17100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6243
  · exact u6244

def b17101 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 28 73 82 160 224 160 416), lower := (rows 289 7 28 73 82 32 64 128 256), losses := [] }

theorem u17101 : Upper (D 8) (R 8) [288,5,24,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17101 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17102 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 28 73 112 162 226 162 418), lower := (rows 289 7 28 73 112 32 64 128 256), losses := [] }

theorem u17102 : Upper (D 8) (R 8) [288,5,24,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17102 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17103 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 28 73 146 224 224 224 480), lower := (rows 289 7 28 73 146 32 64 128 256), losses := [] }

theorem u17103 : Upper (D 8) (R 8) [288,5,24,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17103 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17104 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 28 73 176 226 226 226 482), lower := (rows 289 7 28 73 176 32 64 128 256), losses := [] }

theorem u17104 : Upper (D 8) (R 8) [288,5,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17104 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17105 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 28 73 208 162 226 162 418), lower := (rows 289 7 28 73 208 32 64 128 256), losses := [] }

theorem u17105 : Upper (D 8) (R 8) [288,5,24,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17105 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17106 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 28 74 112 161 225 161 417), lower := (rows 289 7 28 74 112 32 64 128 256), losses := [] }

theorem u17106 : Upper (D 8) (R 8) [288,5,24,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17106 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17107 : Route 9 := (fun mask => (mask,id))

def c17107 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17107 : Upper (D 8) (R 8) [288,5,24,66,160] 13 := by
  apply FastRouting.sound _ _ [288,5,24,66,160] 13 (by decide) (choices 1) [1,64,128] r17107 c17107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6245
  · exact u6246
  · exact u6247

def b17108 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 28 74 208 161 225 161 417), lower := (rows 289 7 28 74 208 32 64 128 256), losses := [] }

theorem u17108 : Upper (D 8) (R 8) [288,5,24,66,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17108 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17109 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 28 104 112 163 195 131 387), lower := (rows 289 7 28 104 112 32 64 128 256), losses := [] }

theorem u17109 : Upper (D 8) (R 8) [288,5,24,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17109 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m17110_128 : Upper (D 8) (R 8) [288,5,24,96,160,128] 13 :=
  permutation_upper _ _ _ [288,5,24,96,160,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6250

def r17110 : Route 9 := (fun mask => (mask,id))

def c17110 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17110 : Upper (D 8) (R 8) [288,5,24,96,160] 13 := by
  apply FastRouting.sound _ _ [288,5,24,96,160] 13 (by decide) (choices 1) [1,2,64,128] r17110 c17110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6248
  · exact u6249
  · exact u6250
  · exact m17110_128

def b17111 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 28 104 208 163 227 163 419), lower := (rows 289 7 28 104 208 32 64 128 256), losses := [] }

theorem u17111 : Upper (D 8) (R 8) [288,5,24,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17111 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17112 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 28 200 208 35 99 163 291), lower := (rows 289 7 28 200 208 32 64 128 256), losses := [] }

theorem u17112 : Upper (D 8) (R 8) [288,5,24,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17112 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17113 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 26 56 224 192 192 448), lower := (rows 289 7 37 26 56 32 64 128 256), losses := [] }

theorem u17113 : Upper (D 8) (R 8) [288,5,33,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17113 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17114 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 26 88 224 224 224 480), lower := (rows 289 7 37 26 88 32 64 128 256), losses := [] }

theorem u17114 : Upper (D 8) (R 8) [288,5,33,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17114 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17115 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 26 112 232 200 200 456), lower := (rows 289 7 37 26 112 32 64 128 256), losses := [] }

theorem u17115 : Upper (D 8) (R 8) [288,5,33,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17115 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17116 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 26 208 232 232 232 488), lower := (rows 289 7 37 26 208 32 64 128 256), losses := [] }

theorem u17116 : Upper (D 8) (R 8) [288,5,33,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17116 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17117 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 42 88 240 208 208 464), lower := (rows 289 7 37 42 88 32 64 128 256), losses := [] }

theorem u17117 : Upper (D 8) (R 8) [288,5,33,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17117 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17118 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 42 208 248 216 216 472), lower := (rows 289 7 37 42 208 32 64 128 256), losses := [] }

theorem u17118 : Upper (D 8) (R 8) [288,5,33,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17118 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17119 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 56 82 232 200 200 456), lower := (rows 289 7 37 56 82 32 64 128 256), losses := [] }

theorem u17119 : Upper (D 8) (R 8) [288,5,33,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17119 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17120 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 56 88 226 194 194 450), lower := (rows 289 7 37 56 88 32 64 128 256), losses := [] }

theorem u17120 : Upper (D 8) (R 8) [288,5,33,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17120 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17121 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 56 208 234 202 202 458), lower := (rows 289 7 37 56 208 32 64 128 256), losses := [] }

theorem u17121 : Upper (D 8) (R 8) [288,5,33,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17121 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17122 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 74 112 184 216 152 408), lower := (rows 289 7 37 74 112 32 64 128 256), losses := [] }

theorem u17122 : Upper (D 8) (R 8) [288,5,33,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17122 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17123 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 74 152 240 240 240 496), lower := (rows 289 7 37 74 152 32 64 128 256), losses := [] }

theorem u17123 : Upper (D 8) (R 8) [288,5,33,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17123 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17124 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 74 176 248 216 216 472), lower := (rows 289 7 37 74 176 32 64 128 256), losses := [] }

theorem u17124 : Upper (D 8) (R 8) [288,5,33,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17124 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17125 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 74 208 184 248 184 440), lower := (rows 289 7 37 74 208 32 64 128 256), losses := [] }

theorem u17125 : Upper (D 8) (R 8) [288,5,33,66,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17125 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17126 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 88 152 226 226 226 482), lower := (rows 289 7 37 88 152 32 64 128 256), losses := [] }

theorem u17126 : Upper (D 8) (R 8) [288,5,33,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17126 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17127 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 88 176 234 202 202 458), lower := (rows 289 7 37 88 176 32 64 128 256), losses := [] }

theorem u17127 : Upper (D 8) (R 8) [288,5,33,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17127 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17128 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 104 208 186 218 154 410), lower := (rows 289 7 37 104 208 32 64 128 256), losses := [] }

theorem u17128 : Upper (D 8) (R 8) [288,5,33,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17128 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17129 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 25 88 224 224 224 480), lower := (rows 289 7 38 25 88 32 64 128 256), losses := [] }

theorem u17129 : Upper (D 8) (R 8) [288,5,34,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17129 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17130 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 25 112 232 200 200 456), lower := (rows 289 7 38 25 112 32 64 128 256), losses := [] }

theorem u17130 : Upper (D 8) (R 8) [288,5,34,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17130 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17131 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 25 208 232 232 232 488), lower := (rows 289 7 38 25 208 32 64 128 256), losses := [] }

theorem u17131 : Upper (D 8) (R 8) [288,5,34,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17131 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17132 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 56 81 232 200 200 456), lower := (rows 289 7 38 56 81 32 64 128 256), losses := [] }

theorem u17132 : Upper (D 8) (R 8) [288,5,34,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17132 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17133 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 56 88 225 193 193 449), lower := (rows 289 7 38 56 88 32 64 128 256), losses := [] }

theorem u17133 : Upper (D 8) (R 8) [288,5,34,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17133 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17134 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 56 208 233 201 201 457), lower := (rows 289 7 38 56 208 32 64 128 256), losses := [] }

theorem u17134 : Upper (D 8) (R 8) [288,5,34,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17134 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17135 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 73 112 184 216 152 408), lower := (rows 289 7 38 73 112 32 64 128 256), losses := [] }

theorem u17135 : Upper (D 8) (R 8) [288,5,34,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17135 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17136 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 73 152 240 240 240 496), lower := (rows 289 7 38 73 152 32 64 128 256), losses := [] }

theorem u17136 : Upper (D 8) (R 8) [288,5,34,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17136 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17137 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 73 176 248 216 216 472), lower := (rows 289 7 38 73 176 32 64 128 256), losses := [] }

theorem u17137 : Upper (D 8) (R 8) [288,5,34,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17137 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17138 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 73 208 184 248 184 440), lower := (rows 289 7 38 73 208 32 64 128 256), losses := [] }

theorem u17138 : Upper (D 8) (R 8) [288,5,34,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17138 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17139 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 88 152 225 225 225 481), lower := (rows 289 7 38 88 152 32 64 128 256), losses := [] }

theorem u17139 : Upper (D 8) (R 8) [288,5,34,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17139 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17140 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 88 176 233 201 201 457), lower := (rows 289 7 38 88 176 32 64 128 256), losses := [] }

theorem u17140 : Upper (D 8) (R 8) [288,5,34,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17140 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17141 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 104 208 185 217 153 409), lower := (rows 289 7 38 104 208 32 64 128 256), losses := [] }

theorem u17141 : Upper (D 8) (R 8) [288,5,34,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17141 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17142 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 30, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 44 25 50 224 192 192 448), lower := (rows 289 7 44 25 50 32 64 128 256), losses := [] }

theorem u17142 : Upper (D 8) (R 8) [288,5,40,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17142 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17143 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 44 25 82 224 224 224 480), lower := (rows 289 7 44 25 82 32 64 128 256), losses := [] }

theorem u17143 : Upper (D 8) (R 8) [288,5,40,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17143 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17144 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 44 25 112 226 194 194 450), lower := (rows 289 7 44 25 112 32 64 128 256), losses := [] }

theorem u17144 : Upper (D 8) (R 8) [288,5,40,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17144 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17145 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 44 25 208 226 226 226 482), lower := (rows 289 7 44 25 208 32 64 128 256), losses := [] }

theorem u17145 : Upper (D 8) (R 8) [288,5,40,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17145 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17146 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 30, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 44 26 49 224 192 192 448), lower := (rows 289 7 44 26 49 32 64 128 256), losses := [] }

theorem u17146 : Upper (D 8) (R 8) [288,5,40,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17146 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17147 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 44 26 81 224 224 224 480), lower := (rows 289 7 44 26 81 32 64 128 256), losses := [] }

theorem u17147 : Upper (D 8) (R 8) [288,5,40,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17147 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17148 : Route 9 := (fun mask => (mask,id))

def c17148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17148 : Upper (D 8) (R 8) [288,5,40,18,96] 13 := by
  apply FastRouting.sound _ _ [288,5,40,18,96] 13 (by decide) (choices 1) [1,64,128] r17148 c17148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6251
  · exact u6252
  · exact u6253

def r17149 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c17149 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17149 : Upper (D 8) (R 8) [288,5,40,18,192] 13 := by
  apply FastRouting.sound _ _ [288,5,40,18,192] 13 (by decide) (choices 1) [1,64] r17149 c17149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6254
  · exact u6255

def b17150 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 44 41 82 240 208 208 464), lower := (rows 289 7 44 41 82 32 64 128 256), losses := [] }

theorem u17150 : Upper (D 8) (R 8) [288,5,40,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17150 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17151 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 44 41 208 242 210 210 466), lower := (rows 289 7 44 41 208 32 64 128 256), losses := [] }

theorem u17151 : Upper (D 8) (R 8) [288,5,40,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17151 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17152 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 44 42 81 240 208 208 464), lower := (rows 289 7 44 42 81 32 64 128 256), losses := [] }

theorem u17152 : Upper (D 8) (R 8) [288,5,40,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17152 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17153 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 44 42 208 241 209 209 465), lower := (rows 289 7 44 42 208 32 64 128 256), losses := [] }

theorem u17153 : Upper (D 8) (R 8) [288,5,40,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17153 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17154 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 44 56 81 226 194 194 450), lower := (rows 289 7 44 56 81 32 64 128 256), losses := [] }

theorem u17154 : Upper (D 8) (R 8) [288,5,40,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17154 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17155 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 44 56 82 225 193 193 449), lower := (rows 289 7 44 56 82 32 64 128 256), losses := [] }

theorem u17155 : Upper (D 8) (R 8) [288,5,40,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17155 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17156 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 44 56 208 227 195 195 451), lower := (rows 289 7 44 56 208 32 64 128 256), losses := [] }

theorem u17156 : Upper (D 8) (R 8) [288,5,40,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17156 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17157 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 44 73 50 240 208 208 464), lower := (rows 289 7 44 73 50 32 64 128 256), losses := [] }

theorem u17157 : Upper (D 8) (R 8) [288,5,40,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17157 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17158 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 44 73 82 176 240 176 432), lower := (rows 289 7 44 73 82 32 64 128 256), losses := [] }

theorem u17158 : Upper (D 8) (R 8) [288,5,40,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17158 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17159 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 44 73 112 178 210 146 402), lower := (rows 289 7 44 73 112 32 64 128 256), losses := [] }

theorem u17159 : Upper (D 8) (R 8) [288,5,40,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17159 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u17159
end Delivery.IrregularNine14.P08
