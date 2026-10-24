import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0088

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15000 : PairBound 9 := { available := 27, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 70 261 168 176 59 91 155 283), lower := (rows 97 70 261 168 176 32 64 128 256), losses := [] }

theorem u15000 : Upper (D 8) (R 8) [96,68,257,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15000 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15001 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 97 70 262 137 176 57 121 185 313), lower := (rows 97 70 262 137 176 32 64 128 256), losses := [] }

theorem u15001 : Upper (D 8) (R 8) [96,68,258,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15001 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15002 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 70 268 137 145 50 114 178 306), lower := (rows 97 70 268 137 145 32 64 128 256), losses := [] }

theorem u15002 : Upper (D 8) (R 8) [96,68,264,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15002 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15003 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 268 137 146 49 113 177 305), lower := (rows 97 70 268 137 146 32 64 128 256), losses := [] }

theorem u15003 : Upper (D 8) (R 8) [96,68,264,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15003 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15004 : Route 9 := (fun mask => (mask,id))

def c15004 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15004 : Upper (D 8) (R 8) [96,68,264,129,160] 13 := by
  apply FastRouting.sound _ _ [96,68,264,129,160] 13 (by decide) (choices 1) [1,2,16] r15004 c15004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5312
  · exact u5313
  · exact u5314

def b15005 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 70 268 138 145 49 113 177 305), lower := (rows 97 70 268 138 145 32 64 128 256), losses := [] }

theorem u15005 : Upper (D 8) (R 8) [96,68,264,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15005 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15006 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 70 268 138 176 49 113 177 305), lower := (rows 97 70 268 138 176 32 64 128 256), losses := [] }

theorem u15006 : Upper (D 8) (R 8) [96,68,264,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15006 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15007 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 268 152 145 35 99 163 291), lower := (rows 97 70 268 152 145 32 64 128 256), losses := [] }

theorem u15007 : Upper (D 8) (R 8) [96,68,264,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15007 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15008 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 268 152 146 33 97 161 289), lower := (rows 97 70 268 152 146 32 64 128 256), losses := [] }

theorem u15008 : Upper (D 8) (R 8) [96,68,264,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15008 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15009 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 268 152 176 35 99 163 291), lower := (rows 97 70 268 152 176 32 64 128 256), losses := [] }

theorem u15009 : Upper (D 8) (R 8) [96,68,264,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15009 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15010 : Route 9 := (fun mask => (mask,id))

def c15010 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15010 : Upper (D 8) (R 8) [96,68,264,160,129] 13 := by
  apply FastRouting.sound _ _ [96,68,264,160,129] 13 (by decide) (choices 1) [1,2,16] r15010 c15010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5315
  · exact u5316
  · exact u5317

def b15011 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 268 168 146 49 113 177 305), lower := (rows 97 70 268 168 146 32 64 128 256), losses := [] }

theorem u15011 : Upper (D 8) (R 8) [96,68,264,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15011 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15012 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 70 268 168 176 51 83 147 275), lower := (rows 97 70 268 168 176 32 64 128 256), losses := [] }

theorem u15012 : Upper (D 8) (R 8) [96,68,264,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15012 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15013 : PairBound 9 := { available := 58, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 70 292 137 145 58 122 186 314), lower := (rows 97 70 292 137 145 32 64 128 256), losses := [] }

theorem u15013 : Upper (D 8) (R 8) [96,68,288,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15013 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15014 : Route 9 := (fun mask => (mask,id))

def c15014 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15014 : Upper (D 8) (R 8) [96,68,288,129,130] 13 := by
  apply FastRouting.sound _ _ [96,68,288,129,130] 13 (by decide) (choices 1) [1,8,16] r15014 c15014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5318
  · exact u5319
  · exact u5320

def b15015 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 70 292 137 152 51 115 179 307), lower := (rows 97 70 292 137 152 32 64 128 256), losses := [] }

theorem u15015 : Upper (D 8) (R 8) [96,68,288,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15015 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15016 : Route 9 := (fun mask => (mask,id))

def c15016 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15016 : Upper (D 8) (R 8) [96,68,288,129,160] 13 := by
  apply FastRouting.sound _ _ [96,68,288,129,160] 13 (by decide) (choices 1) [1,2,8,16] r15016 c15016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5321
  · exact u5322
  · exact u5323
  · exact u5324

def b15017 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 70 292 138 152 49 113 177 305), lower := (rows 97 70 292 138 152 32 64 128 256), losses := [] }

theorem u15017 : Upper (D 8) (R 8) [96,68,288,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15017 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15018 : Route 9 := (fun mask => (mask,id))

def c15018 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15018 : Upper (D 8) (R 8) [96,68,288,130,160] 13 := by
  apply FastRouting.sound _ _ [96,68,288,130,160] 13 (by decide) (choices 1) [1,8,16] r15018 c15018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5325
  · exact u5326
  · exact u5327

def b15019 : PairBound 9 := { available := 35, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 70 292 152 152 35 99 163 291), lower := (rows 97 70 292 152 152 32 64 128 256), losses := [] }

theorem u15019 : Upper (D 8) (R 8) [96,68,288,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15019 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15020 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 70 292 152 176 43 75 139 267), lower := (rows 97 70 292 152 176 32 64 128 256), losses := [] }

theorem u15020 : Upper (D 8) (R 8) [96,68,288,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15020 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15021 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 138 273 60 124 188 316), lower := (rows 97 98 133 138 273 32 64 128 256), losses := [] }

theorem u15021 : Upper (D 8) (R 8) [96,96,129,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15021 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15022 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 138 276 57 121 185 313), lower := (rows 97 98 133 138 276 32 64 128 256), losses := [] }

theorem u15022 : Upper (D 8) (R 8) [96,96,129,130,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15022 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15023 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 138 280 53 117 181 309), lower := (rows 97 98 133 138 280 32 64 128 256), losses := [] }

theorem u15023 : Upper (D 8) (R 8) [96,96,129,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15023 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15024 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 138 304 61 93 157 285), lower := (rows 97 98 133 138 304 32 64 128 256), losses := [] }

theorem u15024 : Upper (D 8) (R 8) [96,96,129,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15024 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15025 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 152 273 46 110 174 302), lower := (rows 97 98 133 152 273 32 64 128 256), losses := [] }

theorem u15025 : Upper (D 8) (R 8) [96,96,129,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15025 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15026 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 152 274 45 109 173 301), lower := (rows 97 98 133 152 274 32 64 128 256), losses := [] }

theorem u15026 : Upper (D 8) (R 8) [96,96,129,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15026 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15027 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 152 304 47 79 143 271), lower := (rows 97 98 133 152 304 32 64 128 256), losses := [] }

theorem u15027 : Upper (D 8) (R 8) [96,96,129,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15027 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15028 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 168 273 62 94 158 286), lower := (rows 97 98 133 168 273 32 64 128 256), losses := [] }

theorem u15028 : Upper (D 8) (R 8) [96,96,129,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15028 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15029 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 168 274 61 93 157 285), lower := (rows 97 98 133 168 274 32 64 128 256), losses := [] }

theorem u15029 : Upper (D 8) (R 8) [96,96,129,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15029 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15030 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 168 276 59 91 155 283), lower := (rows 97 98 133 168 276 32 64 128 256), losses := [] }

theorem u15030 : Upper (D 8) (R 8) [96,96,129,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15030 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15031 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 133 168 280 55 87 151 279), lower := (rows 97 98 133 168 280 32 64 128 256), losses := [] }

theorem u15031 : Upper (D 8) (R 8) [96,96,129,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15031 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15032 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 134 152 273 45 109 173 301), lower := (rows 97 98 134 152 273 32 64 128 256), losses := [] }

theorem u15032 : Upper (D 8) (R 8) [96,96,130,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15032 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15033 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 134 152 304 45 77 141 269), lower := (rows 97 98 134 152 304 32 64 128 256), losses := [] }

theorem u15033 : Upper (D 8) (R 8) [96,96,130,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15033 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15034 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 134 168 273 61 93 157 285), lower := (rows 97 98 134 168 273 32 64 128 256), losses := [] }

theorem u15034 : Upper (D 8) (R 8) [96,96,130,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15034 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15035 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 134 168 276 57 89 153 281), lower := (rows 97 98 134 168 276 32 64 128 256), losses := [] }

theorem u15035 : Upper (D 8) (R 8) [96,96,130,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15035 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15036 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 134 168 280 53 85 149 277), lower := (rows 97 98 134 168 280 32 64 128 256), losses := [] }

theorem u15036 : Upper (D 8) (R 8) [96,96,130,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15036 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15037 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 140 265 176 55 87 151 279), lower := (rows 97 98 140 265 176 32 64 128 256), losses := [] }

theorem u15037 : Upper (D 8) (R 8) [96,96,136,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15037 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15038 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 140 266 176 53 85 149 277), lower := (rows 97 98 140 266 176 32 64 128 256), losses := [] }

theorem u15038 : Upper (D 8) (R 8) [96,96,136,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15038 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15039 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 7 56 280 224 224 224 480), lower := (rows 193 7 7 56 280 32 64 128 256), losses := [] }

theorem u15039 : Upper (D 8) (R 8) [192,5,3,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15039 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15040 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 7 56 336 168 232 168 424), lower := (rows 193 7 7 56 336 32 64 128 256), losses := [] }

theorem u15040 : Upper (D 8) (R 8) [192,5,3,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15040 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15041 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 7 88 176 296 360 424 296), lower := (rows 193 7 7 88 176 32 64 128 256), losses := [] }

theorem u15041 : Upper (D 8) (R 8) [192,5,3,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15041 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15042 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 7 88 304 168 232 168 424), lower := (rows 193 7 7 88 304 32 64 128 256), losses := [] }

theorem u15042 : Upper (D 8) (R 8) [192,5,3,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15042 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15043 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 7 88 400 40 104 168 296), lower := (rows 193 7 7 88 400 32 64 128 256), losses := [] }

theorem u15043 : Upper (D 8) (R 8) [192,5,3,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15043 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15044 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 7 104 176 312 376 440 312), lower := (rows 193 7 7 104 176 32 64 128 256), losses := [] }

theorem u15044 : Upper (D 8) (R 8) [192,5,3,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15044 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15045 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 7 104 280 176 240 176 432), lower := (rows 193 7 7 104 280 32 64 128 256), losses := [] }

theorem u15045 : Upper (D 8) (R 8) [192,5,3,96,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15045 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15046 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 7 104 304 184 248 184 440), lower := (rows 193 7 7 104 304 32 64 128 256), losses := [] }

theorem u15046 : Upper (D 8) (R 8) [192,5,3,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15046 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15047 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 7 104 400 56 120 184 312), lower := (rows 193 7 7 104 400 32 64 128 256), losses := [] }

theorem u15047 : Upper (D 8) (R 8) [192,5,3,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15047 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15048 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 13 26 112 416 480 416 416), lower := (rows 193 7 13 26 112 32 64 128 256), losses := [] }

theorem u15048 : Upper (D 8) (R 8) [192,5,9,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15048 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15049 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 13 26 304 224 224 224 480), lower := (rows 193 7 13 26 304 32 64 128 256), losses := [] }

theorem u15049 : Upper (D 8) (R 8) [192,5,9,18,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15049 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15050 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 13 26 336 160 224 160 416), lower := (rows 193 7 13 26 336 32 64 128 256), losses := [] }

theorem u15050 : Upper (D 8) (R 8) [192,5,9,18,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15050 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15051 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 13 42 112 432 496 432 432), lower := (rows 193 7 13 42 112 32 64 128 256), losses := [] }

theorem u15051 : Upper (D 8) (R 8) [192,5,9,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15051 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15052 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 13 42 304 240 240 240 496), lower := (rows 193 7 13 42 304 32 64 128 256), losses := [] }

theorem u15052 : Upper (D 8) (R 8) [192,5,9,34,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15052 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15053 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 13 42 336 176 240 176 432), lower := (rows 193 7 13 42 336 32 64 128 256), losses := [] }

theorem u15053 : Upper (D 8) (R 8) [192,5,9,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15053 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15054 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 13 56 82 416 480 416 416), lower := (rows 193 7 13 56 82 32 64 128 256), losses := [] }

theorem u15054 : Upper (D 8) (R 8) [192,5,9,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15054 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15055 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 13 56 274 224 224 224 480), lower := (rows 193 7 13 56 274 32 64 128 256), losses := [] }

theorem u15055 : Upper (D 8) (R 8) [192,5,9,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15055 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15056 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 13 56 336 162 226 162 418), lower := (rows 193 7 13 56 336 32 64 128 256), losses := [] }

theorem u15056 : Upper (D 8) (R 8) [192,5,9,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15056 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15057 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 13 74 176 304 368 432 304), lower := (rows 193 7 13 74 176 32 64 128 256), losses := [] }

theorem u15057 : Upper (D 8) (R 8) [192,5,9,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15057 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15058 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 13 74 304 176 240 176 432), lower := (rows 193 7 13 74 304 32 64 128 256), losses := [] }

theorem u15058 : Upper (D 8) (R 8) [192,5,9,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15058 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15059 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 13 74 400 48 112 176 304), lower := (rows 193 7 13 74 400 32 64 128 256), losses := [] }

theorem u15059 : Upper (D 8) (R 8) [192,5,9,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15059 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u15059
end Delivery.IrregularNine14.P08
