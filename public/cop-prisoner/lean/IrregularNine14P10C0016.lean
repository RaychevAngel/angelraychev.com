import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0003
import IrregularNine14P10C0004

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b960 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 388 152 304 33 104 232 360), lower := (rows 35 70 388 152 304 33 64 128 256), losses := [] }

theorem u960 : Upper (D 10) (R 10) [34,68,384,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b960 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b961 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 56, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 388 152 304 40 97 225 353), lower := (rows 35 70 388 152 304 40 64 128 256), losses := [] }

theorem u961 : Upper (D 10) (R 10) [34,68,384,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b961 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b962 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 388 152 304 96 105 169 297), lower := (rows 35 70 388 152 304 96 64 128 256), losses := [] }

theorem u962 : Upper (D 10) (R 10) [34,68,384,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b962 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b963 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 388 152 336 33 104 168 296), lower := (rows 35 70 388 152 336 33 64 128 256), losses := [] }

theorem u963 : Upper (D 10) (R 10) [34,68,384,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b963 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b964 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 388 152 336 40 97 161 289), lower := (rows 35 70 388 152 336 40 64 128 256), losses := [] }

theorem u964 : Upper (D 10) (R 10) [34,68,384,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b964 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b965 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 388 168 304 33 88 216 344), lower := (rows 35 70 388 168 304 33 64 128 256), losses := [] }

theorem u965 : Upper (D 10) (R 10) [34,68,384,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b965 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b966 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 388 168 304 40 81 209 337), lower := (rows 35 70 388 168 304 40 64 128 256), losses := [] }

theorem u966 : Upper (D 10) (R 10) [34,68,384,160,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b966 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b967 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 388 168 304 96 89 153 281), lower := (rows 35 70 388 168 304 96 64 128 256), losses := [] }

theorem u967 : Upper (D 10) (R 10) [34,68,384,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b967 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b968 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 388 168 336 33 120 184 312), lower := (rows 35 70 388 168 336 33 64 128 256), losses := [] }

theorem u968 : Upper (D 10) (R 10) [34,68,384,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b968 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b969 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 388 168 336 40 113 177 305), lower := (rows 35 70 388 168 336 40 64 128 256), losses := [] }

theorem u969 : Upper (D 10) (R 10) [34,68,384,160,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b969 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b970 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 388 168 336 48 105 169 297), lower := (rows 35 70 388 168 336 48 64 128 256), losses := [] }

theorem u970 : Upper (D 10) (R 10) [34,68,384,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b970 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b971 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 44 328 148 33 368 432 304), lower := (rows 35 194 44 328 148 33 64 128 256), losses := [] }

theorem u971 : Upper (D 10) (R 10) [34,192,40,320,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b971 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b972 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 44 328 148 48 353 417 289), lower := (rows 35 194 44 328 148 48 64 128 256), losses := [] }

theorem u972 : Upper (D 10) (R 10) [34,192,40,320,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b972 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b973 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 211, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 194 44 328 148 288 113 177 305), lower := (rows 35 194 44 328 148 288 64 128 256), losses := [] }

theorem u973 : Upper (D 10) (R 10) [34,192,40,320,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b973 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b974 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 44 328 176 33 340 404 276), lower := (rows 35 194 44 328 176 33 64 128 256), losses := [] }

theorem u974 : Upper (D 10) (R 10) [34,192,40,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b974 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b975 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 44 328 176 36 337 401 273), lower := (rows 35 194 44 328 176 36 64 128 256), losses := [] }

theorem u975 : Upper (D 10) (R 10) [34,192,40,320,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b975 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b976 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 44 328 176 48 325 389 261), lower := (rows 35 194 44 328 176 48 64 128 256), losses := [] }

theorem u976 : Upper (D 10) (R 10) [34,192,40,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b976 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b977 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 211, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 194 44 328 176 288 85 149 277), lower := (rows 35 194 44 328 176 288 64 128 256), losses := [] }

theorem u977 : Upper (D 10) (R 10) [34,192,40,320,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b977 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b978 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 44 328 400 33 116 180 308), lower := (rows 35 194 44 328 400 33 64 128 256), losses := [] }

theorem u978 : Upper (D 10) (R 10) [34,192,40,320,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b978 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b979 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 44 328 400 48 101 165 293), lower := (rows 35 194 44 328 400 48 64 128 256), losses := [] }

theorem u979 : Upper (D 10) (R 10) [34,192,40,320,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b979 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b980 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 76 152 273 36 352 416 288), lower := (rows 35 194 76 152 273 36 64 128 256), losses := [] }

theorem u980 : Upper (D 10) (R 10) [34,192,72,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b980 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r981 : Route 9 := (fun mask => (mask,id))

def c981 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u981 : Upper (D 10) (R 10) [34,192,72,144,257,256] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,257,256] 13 (by decide) (choices 1) [4,32] r981 c981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u234
  · exact u235

def b982 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 152 304 33 356 420 292), lower := (rows 35 194 76 152 304 33 64 128 256), losses := [] }

theorem u982 : Upper (D 10) (R 10) [34,192,72,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b982 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b983 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 76 152 304 36 353 417 289), lower := (rows 35 194 76 152 304 36 64 128 256), losses := [] }

theorem u983 : Upper (D 10) (R 10) [34,192,72,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b983 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b984 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 194 76 152 304 288 101 165 293), lower := (rows 35 194 76 152 304 288 64 128 256), losses := [] }

theorem u984 : Upper (D 10) (R 10) [34,192,72,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b984 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b985 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 45, targets := 256 }], pairs := [(0,8)], upper := (rows 35 194 76 168 273 36 368 432 304), lower := (rows 35 194 76 168 273 36 64 128 256), losses := [] }

theorem u985 : Upper (D 10) (R 10) [34,192,72,160,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b985 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b986 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 324, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 76 168 273 48 356 420 292), lower := (rows 35 194 76 168 273 48 64 128 256), losses := [] }

theorem u986 : Upper (D 10) (R 10) [34,192,72,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b986 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r987 : Route 9 := (fun mask => (mask,id))

def c987 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u987 : Upper (D 10) (R 10) [34,192,72,160,257,256] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,257,256] 13 (by decide) (choices 1) [4,16,32] r987 c987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u236
  · exact u237
  · exact u238

def b988 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 33, targets := 256 }], pairs := [(0,8)], upper := (rows 35 194 76 168 276 33 368 432 304), lower := (rows 35 194 76 168 276 33 64 128 256), losses := [] }

theorem u988 : Upper (D 10) (R 10) [34,192,72,160,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b988 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b989 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 76 168 276 48 353 417 289), lower := (rows 35 194 76 168 276 48 64 128 256), losses := [] }

theorem u989 : Upper (D 10) (R 10) [34,192,72,160,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b989 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r990 : Route 9 := (fun mask => (mask,id))

def c990 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u990 : Upper (D 10) (R 10) [34,192,72,160,260,256] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,260,256] 13 (by decide) (choices 1) [1,16,32] r990 c990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u239
  · exact u240
  · exact u241

def b991 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 33, targets := 256 }], pairs := [(0,8)], upper := (rows 35 194 76 168 304 33 340 404 276), lower := (rows 35 194 76 168 304 33 64 128 256), losses := [] }

theorem u991 : Upper (D 10) (R 10) [34,192,72,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b991 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b992 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 45, targets := 256 }], pairs := [(0,8)], upper := (rows 35 194 76 168 304 36 337 401 273), lower := (rows 35 194 76 168 304 36 64 128 256), losses := [] }

theorem u992 : Upper (D 10) (R 10) [34,192,72,160,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b992 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b993 : PairBound 9 := { available := 261, camps := [{ cop := 8, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 76 168 304 48 325 389 261), lower := (rows 35 194 76 168 304 48 64 128 256), losses := [] }

theorem u993 : Upper (D 10) (R 10) [34,192,72,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b993 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b994 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 194 76 168 304 288 85 149 277), lower := (rows 35 194 76 168 304 288 64 128 256), losses := [] }

theorem u994 : Upper (D 10) (R 10) [34,192,72,160,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b994 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b995 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 76 265 176 36 368 432 304), lower := (rows 35 194 76 265 176 36 64 128 256), losses := [] }

theorem u995 : Upper (D 10) (R 10) [34,192,72,257,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b995 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b996 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 265 176 48 356 420 292), lower := (rows 35 194 76 265 176 48 64 128 256), losses := [] }

theorem u996 : Upper (D 10) (R 10) [34,192,72,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b996 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r997 : Route 9 := (fun mask => (mask,id))

def c997 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u997 : Upper (D 10) (R 10) [34,192,72,257,160,256] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,160,256] 13 (by decide) (choices 1) [4,16,32] r997 c997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u242
  · exact u243
  · exact u244

def b998 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 76 265 304 36 240 176 432), lower := (rows 35 194 76 265 304 36 64 128 256), losses := [] }

theorem u998 : Upper (D 10) (R 10) [34,192,72,257,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b998 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b999 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 76 265 304 48 228 164 420), lower := (rows 35 194 76 265 304 48 64 128 256), losses := [] }

theorem u999 : Upper (D 10) (R 10) [34,192,72,257,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b999 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1000 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 348, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 35 194 76 265 304 160 116 180 308), lower := (rows 35 194 76 265 304 160 64 128 256), losses := [] }

theorem u1000 : Upper (D 10) (R 10) [34,192,72,257,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1000 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1001 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 76 265 400 36 112 176 304), lower := (rows 35 194 76 265 400 36 64 128 256), losses := [] }

theorem u1001 : Upper (D 10) (R 10) [34,192,72,257,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1001 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1002 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 76 265 400 48 100 164 292), lower := (rows 35 194 76 265 400 48 64 128 256), losses := [] }

theorem u1002 : Upper (D 10) (R 10) [34,192,72,257,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1002 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1003 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 280 176 33 356 420 292), lower := (rows 35 194 76 280 176 33 64 128 256), losses := [] }

theorem u1003 : Upper (D 10) (R 10) [34,192,72,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1003 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1004 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 76 280 176 36 353 417 289), lower := (rows 35 194 76 280 176 36 64 128 256), losses := [] }

theorem u1004 : Upper (D 10) (R 10) [34,192,72,272,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1004 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1005 : Route 9 := (fun mask => (mask,id))

def c1005 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1005 : Upper (D 10) (R 10) [34,192,72,272,160,256] 13 := by
  apply FastRouting.sound _ _ [34,192,72,272,160,256] 13 (by decide) (choices 1) [1,4,32] r1005 c1005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u245
  · exact u246
  · exact u247

def b1006 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 296 176 33 340 404 276), lower := (rows 35 194 76 296 176 33 64 128 256), losses := [] }

theorem u1006 : Upper (D 10) (R 10) [34,192,72,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1006 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1007 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 76 296 176 36 337 401 273), lower := (rows 35 194 76 296 176 36 64 128 256), losses := [] }

theorem u1007 : Upper (D 10) (R 10) [34,192,72,288,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1007 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1008 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 296 176 48 325 389 261), lower := (rows 35 194 76 296 176 48 64 128 256), losses := [] }

theorem u1008 : Upper (D 10) (R 10) [34,192,72,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1008 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1009 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 215, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 194 76 296 176 288 85 149 277), lower := (rows 35 194 76 296 176 288 64 128 256), losses := [] }

theorem u1009 : Upper (D 10) (R 10) [34,192,72,288,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1009 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1010 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 76 296 273 36 240 176 432), lower := (rows 35 194 76 296 273 36 64 128 256), losses := [] }

theorem u1010 : Upper (D 10) (R 10) [34,192,72,288,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1010 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1011 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8)], upper := (rows 35 194 76 296 273 48 228 164 420), lower := (rows 35 194 76 296 273 48 64 128 256), losses := [] }

theorem u1011 : Upper (D 10) (R 10) [34,192,72,288,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1011 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1012 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 348, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 35 194 76 296 273 160 116 180 308), lower := (rows 35 194 76 296 273 160 64 128 256), losses := [] }

theorem u1012 : Upper (D 10) (R 10) [34,192,72,288,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1012 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1013 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 296 400 33 116 180 308), lower := (rows 35 194 76 296 400 33 64 128 256), losses := [] }

theorem u1013 : Upper (D 10) (R 10) [34,192,72,288,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1013 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1014 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 76 296 400 36 113 177 305), lower := (rows 35 194 76 296 400 36 64 128 256), losses := [] }

theorem u1014 : Upper (D 10) (R 10) [34,192,72,288,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1014 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1015 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8)], upper := (rows 35 194 76 296 400 48 101 165 293), lower := (rows 35 194 76 296 400 48 64 128 256), losses := [] }

theorem u1015 : Upper (D 10) (R 10) [34,192,72,288,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1015 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1016 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 76 392 273 36 112 176 304), lower := (rows 35 194 76 392 273 36 64 128 256), losses := [] }

theorem u1016 : Upper (D 10) (R 10) [34,192,72,384,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1016 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1017 : Route 9 := (fun mask => (mask,id))

def c1017 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1017 : Upper (D 10) (R 10) [34,192,72,384,257,16] 13 := by
  apply FastRouting.sound _ _ [34,192,72,384,257,16] 13 (by decide) (choices 1) [4,32] r1017 c1017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u248
  · exact u249

def b1018 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 392 304 33 116 180 308), lower := (rows 35 194 76 392 304 33 64 128 256), losses := [] }

theorem u1018 : Upper (D 10) (R 10) [34,192,72,384,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1018 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1019 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 76 392 304 36 113 177 305), lower := (rows 35 194 76 392 304 36 64 128 256), losses := [] }

theorem u1019 : Upper (D 10) (R 10) [34,192,72,384,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1019 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u1019
end Delivery.IrregularNine14.P10
