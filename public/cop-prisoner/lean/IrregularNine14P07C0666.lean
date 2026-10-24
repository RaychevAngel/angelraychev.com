import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0472
import IrregularNine14P07C0473

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r39960 : Route 9 := (fun mask => (mask,id))

def c39960 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39960 : Upper (D 7) (R 7) [96,160,72,144,257] 13 := by
  apply FastRouting.sound _ _ [96,160,72,144,257] 13 (by decide) (choices 1) [1,2,4] r39960 c39960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28365
  · exact u28366
  · exact u28367

def r39961 : Route 9 := (fun mask => (mask,id))

def c39961 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39961 : Upper (D 7) (R 7) [96,160,72,144,258] 13 := by
  apply FastRouting.sound _ _ [96,160,72,144,258] 13 (by decide) (choices 1) [1,2,4] r39961 c39961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28368
  · exact u28369
  · exact u28370

def r39962 : Route 9 := (fun mask => (mask,id))

def c39962 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39962 : Upper (D 7) (R 7) [96,160,72,144,260] 13 := by
  apply FastRouting.sound _ _ [96,160,72,144,260] 13 (by decide) (choices 1) [1,2] r39962 c39962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u28371
  · exact u28372

def b39963 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 97 259 7 14 56 240 208 208 464), lower := (rows 97 259 7 14 56 32 64 128 256), losses := [] }

theorem u39963 : Upper (D 7) (R 7) [96,257,3,6,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39963 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39964 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 97 259 7 14 152 240 240 240 496), lower := (rows 97 259 7 14 152 32 64 128 256), losses := [] }

theorem u39964 : Upper (D 7) (R 7) [96,257,3,6,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39964 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39965 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 97 259 7 14 176 248 216 216 472), lower := (rows 97 259 7 14 176 32 64 128 256), losses := [] }

theorem u39965 : Upper (D 7) (R 7) [96,257,3,6,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39966 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 28, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 97 259 7 26 28 224 224 224 480), lower := (rows 97 259 7 26 28 32 64 128 256), losses := [] }

theorem u39966 : Upper (D 7) (R 7) [96,257,3,18,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39966 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39967 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 26 52 232 200 200 456), lower := (rows 97 259 7 26 52 32 64 128 256), losses := [] }

theorem u39967 : Upper (D 7) (R 7) [96,257,3,18,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39968 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 1, region := 4, targets := 192 }], pairs := [(1,5),(2,5),(2,6),(2,7)], upper := (rows 97 259 7 26 56 228 196 196 452), lower := (rows 97 259 7 26 56 32 64 128 256), losses := [] }

theorem u39968 : Upper (D 7) (R 7) [96,257,3,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39969 : PairBound 9 := { available := 232, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 26 148 232 232 232 488), lower := (rows 97 259 7 26 148 32 64 128 256), losses := [] }

theorem u39969 : Upper (D 7) (R 7) [96,257,3,18,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39969 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39970 : PairBound 9 := { available := 228, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 26 152 228 228 228 484), lower := (rows 97 259 7 26 152 32 64 128 256), losses := [] }

theorem u39970 : Upper (D 7) (R 7) [96,257,3,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39971 : PairBound 9 := { available := 204, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 26 176 236 204 204 460), lower := (rows 97 259 7 26 176 32 64 128 256), losses := [] }

theorem u39971 : Upper (D 7) (R 7) [96,257,3,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39971 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39972 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 28 50 232 200 200 456), lower := (rows 97 259 7 28 50 32 64 128 256), losses := [] }

theorem u39972 : Upper (D 7) (R 7) [96,257,3,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39972 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39973 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 1, region := 4, targets := 192 }], pairs := [(1,5),(2,5),(2,6),(2,7)], upper := (rows 97 259 7 28 56 226 194 194 450), lower := (rows 97 259 7 28 56 32 64 128 256), losses := [] }

theorem u39973 : Upper (D 7) (R 7) [96,257,3,20,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39974 : PairBound 9 := { available := 232, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 28 146 232 232 232 488), lower := (rows 97 259 7 28 146 32 64 128 256), losses := [] }

theorem u39974 : Upper (D 7) (R 7) [96,257,3,20,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39975 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 28 152 226 226 226 482), lower := (rows 97 259 7 28 152 32 64 128 256), losses := [] }

theorem u39975 : Upper (D 7) (R 7) [96,257,3,20,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39976 : PairBound 9 := { available := 202, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 28 176 234 202 202 458), lower := (rows 97 259 7 28 176 32 64 128 256), losses := [] }

theorem u39976 : Upper (D 7) (R 7) [96,257,3,20,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39977 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 42 84 184 216 152 408), lower := (rows 97 259 7 42 84 32 64 128 256), losses := [] }

theorem u39977 : Upper (D 7) (R 7) [96,257,3,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39977 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39978 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 42 88 180 212 148 404), lower := (rows 97 259 7 42 88 32 64 128 256), losses := [] }

theorem u39978 : Upper (D 7) (R 7) [96,257,3,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39979 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 42 148 248 216 216 472), lower := (rows 97 259 7 42 148 32 64 128 256), losses := [] }

theorem u39979 : Upper (D 7) (R 7) [96,257,3,34,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39980 : PairBound 9 := { available := 212, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 42 152 244 212 212 468), lower := (rows 97 259 7 42 152 32 64 128 256), losses := [] }

theorem u39980 : Upper (D 7) (R 7) [96,257,3,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39980 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39981 : PairBound 9 := { available := 156, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 42 208 188 220 156 412), lower := (rows 97 259 7 42 208 32 64 128 256), losses := [] }

theorem u39981 : Upper (D 7) (R 7) [96,257,3,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39981 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39982 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 44 88 178 210 146 402), lower := (rows 97 259 7 44 88 32 64 128 256), losses := [] }

theorem u39982 : Upper (D 7) (R 7) [96,257,3,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39982 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39983 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 44 146 248 216 216 472), lower := (rows 97 259 7 44 146 32 64 128 256), losses := [] }

theorem u39983 : Upper (D 7) (R 7) [96,257,3,36,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39984 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 44 152 242 210 210 466), lower := (rows 97 259 7 44 152 32 64 128 256), losses := [] }

theorem u39984 : Upper (D 7) (R 7) [96,257,3,36,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39984 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39985 : PairBound 9 := { available := 154, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 44 208 186 218 154 410), lower := (rows 97 259 7 44 208 32 64 128 256), losses := [] }

theorem u39985 : Upper (D 7) (R 7) [96,257,3,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39985 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39986 : PairBound 9 := { available := 204, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 56 146 236 204 204 460), lower := (rows 97 259 7 56 146 32 64 128 256), losses := [] }

theorem u39986 : Upper (D 7) (R 7) [96,257,3,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39987 : PairBound 9 := { available := 202, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 56 148 234 202 202 458), lower := (rows 97 259 7 56 148 32 64 128 256), losses := [] }

theorem u39987 : Upper (D 7) (R 7) [96,257,3,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39988 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 1, region := 4, targets := 192 }], pairs := [(1,5),(2,5),(2,6),(2,7)], upper := (rows 97 259 7 56 152 230 198 198 454), lower := (rows 97 259 7 56 152 32 64 128 256), losses := [] }

theorem u39988 : Upper (D 7) (R 7) [96,257,3,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39988 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39989 : PairBound 9 := { available := 142, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 56 208 174 206 142 398), lower := (rows 97 259 7 56 208 32 64 128 256), losses := [] }

theorem u39989 : Upper (D 7) (R 7) [96,257,3,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39990 : PairBound 9 := { available := 120, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 138 148 120 120 248 376), lower := (rows 97 259 7 138 148 32 64 128 256), losses := [] }

theorem u39990 : Upper (D 7) (R 7) [96,257,3,130,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39991 : PairBound 9 := { available := 92, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 138 176 124 92 220 348), lower := (rows 97 259 7 138 176 32 64 128 256), losses := [] }

theorem u39991 : Upper (D 7) (R 7) [96,257,3,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39992 : PairBound 9 := { available := 90, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 140 176 122 90 218 346), lower := (rows 97 259 7 140 176 32 64 128 256), losses := [] }

theorem u39992 : Upper (D 7) (R 7) [96,257,3,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39993 : PairBound 9 := { available := 30, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 168 208 62 94 158 286), lower := (rows 97 259 7 168 208 32 64 128 256), losses := [] }

theorem u39993 : Upper (D 7) (R 7) [96,257,3,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39994 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 97 259 13 14 50 240 208 208 464), lower := (rows 97 259 13 14 50 32 64 128 256), losses := [] }

theorem u39994 : Upper (D 7) (R 7) [96,257,9,6,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39994 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39995 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 97 259 13 14 146 240 240 240 496), lower := (rows 97 259 13 14 146 32 64 128 256), losses := [] }

theorem u39995 : Upper (D 7) (R 7) [96,257,9,6,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39995 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39996 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 97 259 13 14 176 242 210 210 466), lower := (rows 97 259 13 14 176 32 64 128 256), losses := [] }

theorem u39996 : Upper (D 7) (R 7) [96,257,9,6,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39996 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39997 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 28, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 97 259 13 26 22 224 224 224 480), lower := (rows 97 259 13 26 22 32 64 128 256), losses := [] }

theorem u39997 : Upper (D 7) (R 7) [96,257,9,18,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39997 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39998 : PairBound 9 := { available := 196, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 259 13 26 50 228 196 196 452), lower := (rows 97 259 13 26 50 32 64 128 256), losses := [] }

theorem u39998 : Upper (D 7) (R 7) [96,257,9,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39999 : Route 9 := (fun mask => (mask,id))

def c39999 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39999 : Upper (D 7) (R 7) [96,257,9,18,36] 13 := by
  apply FastRouting.sound _ _ [96,257,9,18,36] 13 (by decide) (choices 1) [2,64,128] r39999 c39999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28373
  · exact u28374
  · exact u28375

def b40000 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 259 13 26 112 166 198 134 390), lower := (rows 97 259 13 26 112 32 64 128 256), losses := [] }

theorem u40000 : Upper (D 7) (R 7) [96,257,9,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40001 : PairBound 9 := { available := 228, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 259 13 26 146 228 228 228 484), lower := (rows 97 259 13 26 146 32 64 128 256), losses := [] }

theorem u40001 : Upper (D 7) (R 7) [96,257,9,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40002 : Route 9 := (fun mask => (mask,id))

def c40002 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40002 : Upper (D 7) (R 7) [96,257,9,18,132] 13 := by
  apply FastRouting.sound _ _ [96,257,9,18,132] 13 (by decide) (choices 1) [2,64,128] r40002 c40002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28376
  · exact u28377
  · exact u28378

def r40003 : Route 9 := (fun mask => (mask,id))

def c40003 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40003 : Upper (D 7) (R 7) [96,257,9,18,160] 13 := by
  apply FastRouting.sound _ _ [96,257,9,18,160] 13 (by decide) (choices 1) [2,4,64,128] r40003 c40003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28379
  · exact u28380
  · exact u28381
  · exact u28382

def r40004 : Route 9 := (fun mask => (mask,id))

def c40004 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40004 : Upper (D 7) (R 7) [96,257,9,20,34] 13 := by
  apply FastRouting.sound _ _ [96,257,9,20,34] 13 (by decide) (choices 1) [2,64,128] r40004 c40004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28383
  · exact u28384
  · exact u28385

def b40005 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 28, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 259 13 28 112 162 194 130 386), lower := (rows 97 259 13 28 112 32 64 128 256), losses := [] }

theorem u40005 : Upper (D 7) (R 7) [96,257,9,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40006 : Route 9 := (fun mask => (mask,id))

def c40006 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40006 : Upper (D 7) (R 7) [96,257,9,20,130] 13 := by
  apply FastRouting.sound _ _ [96,257,9,20,130] 13 (by decide) (choices 1) [2,64,128] r40006 c40006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28386
  · exact u28387
  · exact u28388

def r40007 : Route 9 := (fun mask => (mask,id))

def c40007 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40007 : Upper (D 7) (R 7) [96,257,9,20,160] 13 := by
  apply FastRouting.sound _ _ [96,257,9,20,160] 13 (by decide) (choices 1) [2,64,128] r40007 c40007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28389
  · exact u28390
  · exact u28391

def b40008 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 232, targets := 1 },{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1),(1,5),(3,0),(4,5)], upper := (rows 97 259 13 42 22 240 208 208 464), lower := (rows 97 259 13 42 22 32 64 128 256), losses := [] }

theorem u40008 : Upper (D 7) (R 7) [96,257,9,34,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40008 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40009 : Route 9 := (fun mask => (mask,id))

def c40009 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40009 : Upper (D 7) (R 7) [96,257,9,34,66] 13 := by
  apply FastRouting.sound _ _ [96,257,9,34,66] 13 (by decide) (choices 1) [4,16,128] r40009 c40009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28392
  · exact u28393
  · exact u28394

def r40010 : Route 9 := (fun mask => (mask,id))

def c40010 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40010 : Upper (D 7) (R 7) [96,257,9,34,68] 13 := by
  apply FastRouting.sound _ _ [96,257,9,34,68] 13 (by decide) (choices 1) [2,16,128] r40010 c40010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28395
  · exact u28396
  · exact u28397

def r40011 : Route 9 := (fun mask => (mask,id))

def c40011 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40011 : Upper (D 7) (R 7) [96,257,9,34,130] 13 := by
  apply FastRouting.sound _ _ [96,257,9,34,130] 13 (by decide) (choices 1) [4,16,64,128] r40011 c40011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28398
  · exact u28399
  · exact u28400
  · exact u28401

def r40012 : Route 9 := (fun mask => (mask,id))

def c40012 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40012 : Upper (D 7) (R 7) [96,257,9,34,132] 13 := by
  apply FastRouting.sound _ _ [96,257,9,34,132] 13 (by decide) (choices 1) [2,16,64,128] r40012 c40012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28402
  · exact u28403
  · exact u28404
  · exact u28405

def r40013 : Route 9 := (fun mask => (mask,id))

def c40013 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40013 : Upper (D 7) (R 7) [96,257,9,34,192] 13 := by
  apply FastRouting.sound _ _ [96,257,9,34,192] 13 (by decide) (choices 1) [2,4,16,128] r40013 c40013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28406
  · exact u28407
  · exact u28408
  · exact u28409

def b40014 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 97 259 13 44 82 178 210 146 402), lower := (rows 97 259 13 44 82 32 64 128 256), losses := [] }

theorem u40014 : Upper (D 7) (R 7) [96,257,9,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40014 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40015 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 97 259 13 44 146 242 210 210 466), lower := (rows 97 259 13 44 146 32 64 128 256), losses := [] }

theorem u40015 : Upper (D 7) (R 7) [96,257,9,36,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40016 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 97 259 13 44 208 178 210 146 402), lower := (rows 97 259 13 44 208 32 64 128 256), losses := [] }

theorem u40016 : Upper (D 7) (R 7) [96,257,9,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40017 : Route 9 := (fun mask => (mask,id))

def c40017 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40017 : Upper (D 7) (R 7) [96,257,9,48,6] 13 := by
  apply FastRouting.sound _ _ [96,257,9,48,6] 13 (by decide) (choices 1) [2,64,128] r40017 c40017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28410
  · exact u28411
  · exact u28412

def r40018 : Route 9 := (fun mask => (mask,id))

def c40018 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40018 : Upper (D 7) (R 7) [96,257,9,48,66] 13 := by
  apply FastRouting.sound _ _ [96,257,9,48,66] 13 (by decide) (choices 1) [2,4,128] r40018 c40018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28413
  · exact u28414
  · exact u28415

def b40019 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 28, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 259 13 56 84 162 194 130 386), lower := (rows 97 259 13 56 84 32 64 128 256), losses := [] }

theorem u40019 : Upper (D 7) (R 7) [96,257,9,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u40019
end Delivery.IrregularNine14.P07
