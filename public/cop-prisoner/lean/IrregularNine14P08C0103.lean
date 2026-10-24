import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0012
import IrregularNine14P08C0013

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6180 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 98 44 88 145 36 225 161 417), lower := (rows 259 98 44 88 145 36 64 128 256), losses := [] }

theorem u6180 : Upper (D 8) (R 8) [258,96,40,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6180 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6181 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 44 88 145 160 101 165 293), lower := (rows 259 98 44 88 145 160 64 128 256), losses := [] }

theorem u6181 : Upper (D 8) (R 8) [258,96,40,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6181 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6182 : Route 9 := (fun mask => (mask,id))

def c6182 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6182 : Upper (D 8) (R 8) [258,96,40,80,160,1] 13 := by
  apply FastRouting.sound _ _ [258,96,40,80,160,1] 13 (by decide) (choices 1) [1,4,128] r6182 c6182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u769
  · exact u770
  · exact u771

def b6183 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 98 44 88 176 36 193 129 385), lower := (rows 259 98 44 88 176 36 64 128 256), losses := [] }

theorem u6183 : Upper (D 8) (R 8) [258,96,40,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6183 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6184 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 44 88 176 160 69 133 261), lower := (rows 259 98 44 88 176 160 64 128 256), losses := [] }

theorem u6184 : Upper (D 8) (R 8) [258,96,40,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6184 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6185 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 44 137 84 33 240 176 432), lower := (rows 259 98 44 137 84 33 64 128 256), losses := [] }

theorem u6185 : Upper (D 8) (R 8) [258,96,40,129,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6185 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6186 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 98 44 137 84 48 225 161 417), lower := (rows 259 98 44 137 84 48 64 128 256), losses := [] }

theorem u6186 : Upper (D 8) (R 8) [258,96,40,129,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6186 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6187 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 44 137 84 160 113 177 305), lower := (rows 259 98 44 137 84 160 64 128 256), losses := [] }

theorem u6187 : Upper (D 8) (R 8) [258,96,40,129,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6187 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6188 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 44 137 176 33 84 212 340), lower := (rows 259 98 44 137 176 33 64 128 256), losses := [] }

theorem u6188 : Upper (D 8) (R 8) [258,96,40,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6188 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6189 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 259 98 44 137 176 36 81 209 337), lower := (rows 259 98 44 137 176 36 64 128 256), losses := [] }

theorem u6189 : Upper (D 8) (R 8) [258,96,40,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6189 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6190 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 259 98 44 137 176 48 69 197 325), lower := (rows 259 98 44 137 176 48 64 128 256), losses := [] }

theorem u6190 : Upper (D 8) (R 8) [258,96,40,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6190 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6191 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 44 137 176 96 85 149 277), lower := (rows 259 98 44 137 176 96 64 128 256), losses := [] }

theorem u6191 : Upper (D 8) (R 8) [258,96,40,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6191 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6192 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 44 137 208 33 116 180 308), lower := (rows 259 98 44 137 208 33 64 128 256), losses := [] }

theorem u6192 : Upper (D 8) (R 8) [258,96,40,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6192 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6193 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 259 98 44 137 208 36 113 177 305), lower := (rows 259 98 44 137 208 36 64 128 256), losses := [] }

theorem u6193 : Upper (D 8) (R 8) [258,96,40,129,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6193 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6194 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 259 98 44 137 208 48 101 165 293), lower := (rows 259 98 44 137 208 48 64 128 256), losses := [] }

theorem u6194 : Upper (D 8) (R 8) [258,96,40,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6194 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6195 : Route 9 := (fun mask => (mask,id))

def c6195 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6195 : Upper (D 8) (R 8) [258,96,40,192,129,1] 13 := by
  apply FastRouting.sound _ _ [258,96,40,192,129,1] 13 (by decide) (choices 1) [4,16,32] r6195 c6195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u772
  · exact u773
  · exact u774

def b6196 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 259 98 44 200 145 36 113 177 305), lower := (rows 259 98 44 200 145 36 64 128 256), losses := [] }

theorem u6196 : Upper (D 8) (R 8) [258,96,40,192,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6196 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6197 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 259 98 44 200 145 48 101 165 293), lower := (rows 259 98 44 200 145 48 64 128 256), losses := [] }

theorem u6197 : Upper (D 8) (R 8) [258,96,40,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6197 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6198 : Route 9 := (fun mask => (mask,id))

def c6198 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6198 : Upper (D 8) (R 8) [258,96,40,192,160,1] 13 := by
  apply FastRouting.sound _ _ [258,96,40,192,160,1] 13 (by decide) (choices 1) [1,4,16] r6198 c6198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u775
  · exact u776
  · exact u777

def b6199 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 259 98 44 200 176 36 81 145 273), lower := (rows 259 98 44 200 176 36 64 128 256), losses := [] }

theorem u6199 : Upper (D 8) (R 8) [258,96,40,192,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6199 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6200 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 259 98 44 200 176 48 69 133 261), lower := (rows 259 98 44 200 176 48 64 128 256), losses := [] }

theorem u6200 : Upper (D 8) (R 8) [258,96,40,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6200 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6201 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 259 98 76 137 176 33 116 180 308), lower := (rows 259 98 76 137 176 33 64 128 256), losses := [] }

theorem u6201 : Upper (D 8) (R 8) [258,96,72,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6201 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6202 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 259 98 76 137 176 36 113 177 305), lower := (rows 259 98 76 137 176 36 64 128 256), losses := [] }

theorem u6202 : Upper (D 8) (R 8) [258,96,72,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6202 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6203 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 259 98 76 137 176 48 101 165 293), lower := (rows 259 98 76 137 176 48 64 128 256), losses := [] }

theorem u6203 : Upper (D 8) (R 8) [258,96,72,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6203 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6204 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 259 98 76 168 145 33 116 180 308), lower := (rows 259 98 76 168 145 33 64 128 256), losses := [] }

theorem u6204 : Upper (D 8) (R 8) [258,96,72,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6204 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6205 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 259 98 76 168 145 36 113 177 305), lower := (rows 259 98 76 168 145 36 64 128 256), losses := [] }

theorem u6205 : Upper (D 8) (R 8) [258,96,72,160,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6205 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6206 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 259 98 76 168 145 48 101 165 293), lower := (rows 259 98 76 168 145 48 64 128 256), losses := [] }

theorem u6206 : Upper (D 8) (R 8) [258,96,72,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6206 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6207 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 44, targets := 64 }], pairs := [(2,6)], upper := (rows 259 194 13 44 112 33 240 176 432), lower := (rows 259 194 13 44 112 33 64 128 256), losses := [] }

theorem u6207 : Upper (D 8) (R 8) [258,192,9,36,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6207 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6208 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 194 13 44 112 48 225 161 417), lower := (rows 259 194 13 44 112 48 64 128 256), losses := [] }

theorem u6208 : Upper (D 8) (R 8) [258,192,9,36,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6208 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6209 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 259 194 13 44 112 160 113 177 305), lower := (rows 259 194 13 44 112 160 64 128 256), losses := [] }

theorem u6209 : Upper (D 8) (R 8) [258,192,9,36,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6209 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6210 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 214, targets := 1 }], pairs := [(1,0)], upper := (rows 259 194 28 41 112 33 228 164 420), lower := (rows 259 194 28 41 112 33 64 128 256), losses := [] }

theorem u6210 : Upper (D 8) (R 8) [258,192,24,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6210 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6211 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 194 28 41 112 36 225 161 417), lower := (rows 259 194 28 41 112 36 64 128 256), losses := [] }

theorem u6211 : Upper (D 8) (R 8) [258,192,24,33,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6211 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6212 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 84, targets := 128 }], pairs := [(2,7)], upper := (rows 259 194 28 41 112 160 101 165 293), lower := (rows 259 194 28 41 112 160 64 128 256), losses := [] }

theorem u6212 : Upper (D 8) (R 8) [258,192,24,33,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6212 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6213 : Route 9 := (fun mask => (mask,id))

def c6213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6213 : Upper (D 8) (R 8) [258,192,24,96,160,1] 13 := by
  apply FastRouting.sound _ _ [258,192,24,96,160,1] 13 (by decide) (choices 1) [1,4,32] r6213 c6213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u778
  · exact u779
  · exact u780

def b6214 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 194 28 104 176 36 97 161 289), lower := (rows 259 194 28 104 176 36 64 128 256), losses := [] }

theorem u6214 : Upper (D 8) (R 8) [258,192,24,96,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6214 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6215 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 194 37 56 84 33 232 168 424), lower := (rows 259 194 37 56 84 33 64 128 256), losses := [] }

theorem u6215 : Upper (D 8) (R 8) [258,192,33,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6215 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6216 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 259 194 37 56 84 40 225 161 417), lower := (rows 259 194 37 56 84 40 64 128 256), losses := [] }

theorem u6216 : Upper (D 8) (R 8) [258,192,33,48,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6216 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6217 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 88, targets := 128 }], pairs := [(3,7)], upper := (rows 259 194 37 56 84 160 105 169 297), lower := (rows 259 194 37 56 84 160 64 128 256), losses := [] }

theorem u6217 : Upper (D 8) (R 8) [258,192,33,48,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6217 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6218 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 194 37 76 152 33 112 176 304), lower := (rows 259 194 37 76 152 33 64 128 256), losses := [] }

theorem u6218 : Upper (D 8) (R 8) [258,192,33,68,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6218 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6219 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 194 37 76 152 48 97 161 289), lower := (rows 259 194 37 76 152 48 64 128 256), losses := [] }

theorem u6219 : Upper (D 8) (R 8) [258,192,33,68,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6219 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6220 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 194 37 76 176 33 120 184 312), lower := (rows 259 194 37 76 176 33 64 128 256), losses := [] }

theorem u6220 : Upper (D 8) (R 8) [258,192,33,68,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6220 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6221 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 259 194 37 76 176 40 113 177 305), lower := (rows 259 194 37 76 176 40 64 128 256), losses := [] }

theorem u6221 : Upper (D 8) (R 8) [258,192,33,68,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6221 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6222 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 259 194 37 76 176 48 105 169 297), lower := (rows 259 194 37 76 176 48 64 128 256), losses := [] }

theorem u6222 : Upper (D 8) (R 8) [258,192,33,68,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6222 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6223 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 194 37 88 176 33 108 172 300), lower := (rows 259 194 37 88 176 33 64 128 256), losses := [] }

theorem u6223 : Upper (D 8) (R 8) [258,192,33,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6223 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6224 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 259 194 37 88 176 36 105 169 297), lower := (rows 259 194 37 88 176 36 64 128 256), losses := [] }

theorem u6224 : Upper (D 8) (R 8) [258,192,33,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6224 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6225 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 259 194 37 88 176 40 101 165 293), lower := (rows 259 194 37 88 176 40 64 128 256), losses := [] }

theorem u6225 : Upper (D 8) (R 8) [258,192,33,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6225 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6226 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 259 194 37 104 176 33 92 156 284), lower := (rows 259 194 37 104 176 33 64 128 256), losses := [] }

theorem u6226 : Upper (D 8) (R 8) [258,192,33,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6226 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6227 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 259 194 37 104 176 36 89 153 281), lower := (rows 259 194 37 104 176 36 64 128 256), losses := [] }

theorem u6227 : Upper (D 8) (R 8) [258,192,33,96,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6227 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6228 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 259 194 37 104 176 40 85 149 277), lower := (rows 259 194 37 104 176 40 64 128 256), losses := [] }

theorem u6228 : Upper (D 8) (R 8) [258,192,33,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6228 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6229 : Route 9 := (fun mask => (mask,id))

def c6229 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6229 : Upper (D 8) (R 8) [258,192,40,80,160,1] 13 := by
  apply FastRouting.sound _ _ [258,192,40,80,160,1] 13 (by decide) (choices 1) [1,4,32] r6229 c6229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u781
  · exact u782
  · exact u783

def b6230 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 194 44 88 176 36 97 161 289), lower := (rows 259 194 44 88 176 36 64 128 256), losses := [] }

theorem u6230 : Upper (D 8) (R 8) [258,192,40,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6230 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6231 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 14 56 208 33 224 224 480), lower := (rows 289 7 14 56 208 33 64 128 256), losses := [] }

theorem u6231 : Upper (D 8) (R 8) [288,5,10,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6231 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6232 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 14 56 208 96 225 161 417), lower := (rows 289 7 14 56 208 96 64 128 256), losses := [] }

theorem u6232 : Upper (D 8) (R 8) [288,5,10,48,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6232 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6233 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 14 88 176 33 224 224 480), lower := (rows 289 7 14 88 176 33 64 128 256), losses := [] }

theorem u6233 : Upper (D 8) (R 8) [288,5,10,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6233 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6234 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 14 88 176 96 225 161 417), lower := (rows 289 7 14 88 176 96 64 128 256), losses := [] }

theorem u6234 : Upper (D 8) (R 8) [288,5,10,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6234 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6235 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 14 88 176 160 97 225 353), lower := (rows 289 7 14 88 176 160 64 128 256), losses := [] }

theorem u6235 : Upper (D 8) (R 8) [288,5,10,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6235 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6236 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 14 104 176 33 208 208 464), lower := (rows 289 7 14 104 176 33 64 128 256), losses := [] }

theorem u6236 : Upper (D 8) (R 8) [288,5,10,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6236 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6237 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 289 7 14 104 176 48 193 193 449), lower := (rows 289 7 14 104 176 48 64 128 256), losses := [] }

theorem u6237 : Upper (D 8) (R 8) [288,5,10,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6237 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6238 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 14 104 176 96 209 145 401), lower := (rows 289 7 14 104 176 96 64 128 256), losses := [] }

theorem u6238 : Upper (D 8) (R 8) [288,5,10,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6238 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6239 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 14 104 176 160 81 209 337), lower := (rows 289 7 14 104 176 160 64 128 256), losses := [] }

theorem u6239 : Upper (D 8) (R 8) [288,5,10,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6239 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u6239
end Delivery.IrregularNine14.P08
