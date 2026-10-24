import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0026

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4080 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 280 145 226 226 226 482), lower := (rows 97 7 13 280 145 32 64 128 256), losses := [] }

theorem u4080 : Upper (D 3) (R 3) [96,5,9,272,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4080
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4081 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 280 146 225 225 225 481), lower := (rows 97 7 13 280 146 32 64 128 256), losses := [] }

theorem u4081 : Upper (D 3) (R 3) [96,5,9,272,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4081
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4082 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 13 280 176 227 195 195 451), lower := (rows 97 7 13 280 176 32 64 128 256), losses := [] }

theorem u4082 : Upper (D 3) (R 3) [96,5,9,272,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4082
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4083 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 296 82 177 209 145 401), lower := (rows 97 7 13 296 82 32 64 128 256), losses := [] }

theorem u4083 : Upper (D 3) (R 3) [96,5,9,288,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4083
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4084 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 296 145 242 210 210 466), lower := (rows 97 7 13 296 145 32 64 128 256), losses := [] }

theorem u4084 : Upper (D 3) (R 3) [96,5,9,288,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4084
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4085 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 296 146 241 209 209 465), lower := (rows 97 7 13 296 146 32 64 128 256), losses := [] }

theorem u4085 : Upper (D 3) (R 3) [96,5,9,288,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4085
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4086 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 296 208 179 211 147 403), lower := (rows 97 7 13 296 208 32 64 128 256), losses := [] }

theorem u4086 : Upper (D 3) (R 3) [96,5,9,288,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4086
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4087 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 392 50 241 209 209 465), lower := (rows 97 7 13 392 50 32 64 128 256), losses := [] }

theorem u4087 : Upper (D 3) (R 3) [96,5,9,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4087
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4088 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 392 145 114 114 242 370), lower := (rows 97 7 13 392 145 32 64 128 256), losses := [] }

theorem u4088 : Upper (D 3) (R 3) [96,5,9,384,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4088
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4089 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 392 146 113 113 241 369), lower := (rows 97 7 13 392 146 32 64 128 256), losses := [] }

theorem u4089 : Upper (D 3) (R 3) [96,5,9,384,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4089
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4090 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 392 176 115 83 211 339), lower := (rows 97 7 13 392 176 32 64 128 256), losses := [] }

theorem u4090 : Upper (D 3) (R 3) [96,5,9,384,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4090
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4091 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 25 145 480 480 480 480), lower := (rows 97 7 14 25 145 32 64 128 256), losses := [] }

theorem u4091 : Upper (D 3) (R 3) [96,5,10,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4091
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4092 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 25 176 481 449 449 449), lower := (rows 97 7 14 25 176 32 64 128 256), losses := [] }

theorem u4092 : Upper (D 3) (R 3) [96,5,10,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4092
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4093 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 25 273 224 224 224 480), lower := (rows 97 7 14 25 273 32 64 128 256), losses := [] }

theorem u4093 : Upper (D 3) (R 3) [96,5,10,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4093
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4094 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 25 304 225 193 193 449), lower := (rows 97 7 14 25 304 32 64 128 256), losses := [] }

theorem u4094 : Upper (D 3) (R 3) [96,5,10,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4094
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4095 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 25 400 225 225 225 481), lower := (rows 97 7 14 25 400 32 64 128 256), losses := [] }

theorem u4095 : Upper (D 3) (R 3) [96,5,10,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4095
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4096 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 41 145 496 464 464 464), lower := (rows 97 7 14 41 145 32 64 128 256), losses := [] }

theorem u4096 : Upper (D 3) (R 3) [96,5,10,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4096
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4097 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 41 208 433 465 401 401), lower := (rows 97 7 14 41 208 32 64 128 256), losses := [] }

theorem u4097 : Upper (D 3) (R 3) [96,5,10,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4097
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4098 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 41 273 240 208 208 464), lower := (rows 97 7 14 41 273 32 64 128 256), losses := [] }

theorem u4098 : Upper (D 3) (R 3) [96,5,10,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4098
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4099 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 41 336 177 209 145 401), lower := (rows 97 7 14 41 336 32 64 128 256), losses := [] }

theorem u4099 : Upper (D 3) (R 3) [96,5,10,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4099
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4100 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 41 400 241 209 209 465), lower := (rows 97 7 14 41 400 32 64 128 256), losses := [] }

theorem u4100 : Upper (D 3) (R 3) [96,5,10,33,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4100
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4101 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 14 56 145 481 449 449 449), lower := (rows 97 7 14 56 145 32 64 128 256), losses := [] }

theorem u4101 : Upper (D 3) (R 3) [96,5,10,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4101
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4102 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 14 56 208 417 449 385 385), lower := (rows 97 7 14 56 208 32 64 128 256), losses := [] }

theorem u4102 : Upper (D 3) (R 3) [96,5,10,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4102
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4103 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 14 56 273 225 193 193 449), lower := (rows 97 7 14 56 273 32 64 128 256), losses := [] }

theorem u4103 : Upper (D 3) (R 3) [96,5,10,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4103
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4104 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 14 56 336 161 193 129 385), lower := (rows 97 7 14 56 336 32 64 128 256), losses := [] }

theorem u4104 : Upper (D 3) (R 3) [96,5,10,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4104
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4105 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 14 56 400 225 193 193 449), lower := (rows 97 7 14 56 400 32 64 128 256), losses := [] }

theorem u4105 : Upper (D 3) (R 3) [96,5,10,48,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4105
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4106 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 14 104 145 433 465 401 401), lower := (rows 97 7 14 104 145 32 64 128 256), losses := [] }

theorem u4106 : Upper (D 3) (R 3) [96,5,10,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4106
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4107 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 14 104 273 177 209 145 401), lower := (rows 97 7 14 104 273 32 64 128 256), losses := [] }

theorem u4107 : Upper (D 3) (R 3) [96,5,10,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4107
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4108 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 14 104 400 177 209 145 401), lower := (rows 97 7 14 104 400 32 64 128 256), losses := [] }

theorem u4108 : Upper (D 3) (R 3) [96,5,10,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4108
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4109 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 137 145 368 368 496 368), lower := (rows 97 7 14 137 145 32 64 128 256), losses := [] }

theorem u4109 : Upper (D 3) (R 3) [96,5,10,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4109
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4110 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 137 176 369 337 465 337), lower := (rows 97 7 14 137 176 32 64 128 256), losses := [] }

theorem u4110 : Upper (D 3) (R 3) [96,5,10,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4110
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4111 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 137 273 240 240 240 496), lower := (rows 97 7 14 137 273 32 64 128 256), losses := [] }

theorem u4111 : Upper (D 3) (R 3) [96,5,10,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4111
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4112 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 137 304 241 209 209 465), lower := (rows 97 7 14 137 304 32 64 128 256), losses := [] }

theorem u4112 : Upper (D 3) (R 3) [96,5,10,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4112
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4113 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 137 400 113 113 241 369), lower := (rows 97 7 14 137 400 32 64 128 256), losses := [] }

theorem u4113 : Upper (D 3) (R 3) [96,5,10,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4113
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4114 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 152 49 481 449 449 449), lower := (rows 97 7 14 152 49 32 64 128 256), losses := [] }

theorem u4114 : Upper (D 3) (R 3) [96,5,10,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4114
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4115 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 14 152 112 417 449 385 385), lower := (rows 97 7 14 152 112 32 64 128 256), losses := [] }

theorem u4115 : Upper (D 3) (R 3) [96,5,10,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4115
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4116 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 152 145 353 353 481 353), lower := (rows 97 7 14 152 145 32 64 128 256), losses := [] }

theorem u4116 : Upper (D 3) (R 3) [96,5,10,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4116
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4117 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 152 176 353 321 449 321), lower := (rows 97 7 14 152 176 32 64 128 256), losses := [] }

theorem u4117 : Upper (D 3) (R 3) [96,5,10,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4117
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4118 : Route 9 := (fun mask => (mask,id))

def c4118 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4118 : Upper (D 3) (R 3) [96,5,10,144,257] 13 := by
  apply FastRouting.sound _ _ [96,5,10,144,257] 13 (by decide) (choices 1) [1,64,128] r4118 c4118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1606
  · exact u1607
  · exact u1608

def r4119 : Route 9 := (fun mask => (mask,id))

def c4119 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4119 : Upper (D 3) (R 3) [96,5,10,144,288] 13 := by
  apply FastRouting.sound _ _ [96,5,10,144,288] 13 (by decide) (choices 1) [1,64,128] r4119 c4119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1609
  · exact u1610
  · exact u1611

def b4120 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 152 400 97 97 225 353), lower := (rows 97 7 14 152 400 32 64 128 256), losses := [] }

theorem u4120 : Upper (D 3) (R 3) [96,5,10,144,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4120
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4121 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 14 168 145 369 337 465 337), lower := (rows 97 7 14 168 145 32 64 128 256), losses := [] }

theorem u4121 : Upper (D 3) (R 3) [96,5,10,160,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4121
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4122 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 14 168 208 305 337 401 273), lower := (rows 97 7 14 168 208 32 64 128 256), losses := [] }

theorem u4122 : Upper (D 3) (R 3) [96,5,10,160,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4122
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4123 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 14 168 273 241 209 209 465), lower := (rows 97 7 14 168 273 32 64 128 256), losses := [] }

theorem u4123 : Upper (D 3) (R 3) [96,5,10,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4123
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4124 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 14 168 336 177 209 145 401), lower := (rows 97 7 14 168 336 32 64 128 256), losses := [] }

theorem u4124 : Upper (D 3) (R 3) [96,5,10,160,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4124
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4125 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 14 168 400 113 81 209 337), lower := (rows 97 7 14 168 400 32 64 128 256), losses := [] }

theorem u4125 : Upper (D 3) (R 3) [96,5,10,160,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4125
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4126 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 265 145 240 240 240 496), lower := (rows 97 7 14 265 145 32 64 128 256), losses := [] }

theorem u4126 : Upper (D 3) (R 3) [96,5,10,257,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4126
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4127 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 265 176 241 209 209 465), lower := (rows 97 7 14 265 176 32 64 128 256), losses := [] }

theorem u4127 : Upper (D 3) (R 3) [96,5,10,257,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4127
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4128 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 280 49 225 193 193 449), lower := (rows 97 7 14 280 49 32 64 128 256), losses := [] }

theorem u4128 : Upper (D 3) (R 3) [96,5,10,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4128
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4129 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 14 280 112 161 193 129 385), lower := (rows 97 7 14 280 112 32 64 128 256), losses := [] }

theorem u4129 : Upper (D 3) (R 3) [96,5,10,272,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4129
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4130 : Route 9 := (fun mask => (mask,id))

def c4130 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4130 : Upper (D 3) (R 3) [96,5,10,272,129] 13 := by
  apply FastRouting.sound _ _ [96,5,10,272,129] 13 (by decide) (choices 1) [1,64,128] r4130 c4130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1612
  · exact u1613
  · exact u1614

def r4131 : Route 9 := (fun mask => (mask,id))

def c4131 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4131 : Upper (D 3) (R 3) [96,5,10,272,160] 13 := by
  apply FastRouting.sound _ _ [96,5,10,272,160] 13 (by decide) (choices 1) [1,64,128] r4131 c4131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1615
  · exact u1616
  · exact u1617

def b4132 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 14 296 145 241 209 209 465), lower := (rows 97 7 14 296 145 32 64 128 256), losses := [] }

theorem u4132 : Upper (D 3) (R 3) [96,5,10,288,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4132
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4133 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 14 296 208 177 209 145 401), lower := (rows 97 7 14 296 208 32 64 128 256), losses := [] }

theorem u4133 : Upper (D 3) (R 3) [96,5,10,288,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4133
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4134 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 392 49 241 209 209 465), lower := (rows 97 7 14 392 49 32 64 128 256), losses := [] }

theorem u4134 : Upper (D 3) (R 3) [96,5,10,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4134
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4135 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 14 392 112 177 209 145 401), lower := (rows 97 7 14 392 112 32 64 128 256), losses := [] }

theorem u4135 : Upper (D 3) (R 3) [96,5,10,384,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4135
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4136 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 392 145 113 113 241 369), lower := (rows 97 7 14 392 145 32 64 128 256), losses := [] }

theorem u4136 : Upper (D 3) (R 3) [96,5,10,384,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4136
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4137 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 392 176 113 81 209 337), lower := (rows 97 7 14 392 176 32 64 128 256), losses := [] }

theorem u4137 : Upper (D 3) (R 3) [96,5,10,384,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4137
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4138 : PairBound 9 := { available := 450, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 28 41 145 482 450 450 450), lower := (rows 97 7 28 41 145 32 64 128 256), losses := [] }

theorem u4138 : Upper (D 3) (R 3) [96,5,24,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4138
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4139 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 28 41 146 481 449 449 449), lower := (rows 97 7 28 41 146 32 64 128 256), losses := [] }

theorem u4139 : Upper (D 3) (R 3) [96,5,24,33,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4139
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u4139
end Delivery.IrregularNine14.P03
