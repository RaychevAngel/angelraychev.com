import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0104

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21180 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 134 25 276 33 100 228 356), lower := (rows 35 74 134 25 276 33 64 128 256), losses := [] }

theorem u21180 : Upper (D 6) (R 6) [34,72,130,17,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21181 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,2),(3,6)], upper := (rows 35 74 134 25 276 36 97 225 353), lower := (rows 35 74 134 25 276 36 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 16 32 65 129 257), good := (rows 483 74 130 475 272 32 64 128 256) },{ target := 6, region := (rows 5 2 4 24 16 52 0 128 256), good := (rows 35 10 167 57 317 37 0 128 256) }] }

theorem u21181 : Upper (D 6) (R 6) [34,72,130,17,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21182 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 134 25 276 96 101 165 293), lower := (rows 35 74 134 25 276 96 64 128 256), losses := [] }

theorem u21182 : Upper (D 6) (R 6) [34,72,130,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21183 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 198, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 74 134 25 304 33 68 196 324), lower := (rows 35 74 134 25 304 33 64 128 256), losses := [] }

theorem u21183 : Upper (D 6) (R 6) [34,72,130,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21184 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 198, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 35 74 134 25 304 36 69 197 325), lower := (rows 35 74 134 25 304 36 64 128 256), losses := [] }

theorem u21184 : Upper (D 6) (R 6) [34,72,130,17,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21185 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 134 25 304 96 69 133 261), lower := (rows 35 74 134 25 304 96 64 128 256), losses := [] }

theorem u21185 : Upper (D 6) (R 6) [34,72,130,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21186 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 134 25 336 33 100 164 292), lower := (rows 35 74 134 25 336 33 64 128 256), losses := [] }

theorem u21186 : Upper (D 6) (R 6) [34,72,130,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21186 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21187 : Route 9 := (fun mask => (mask,id))

def c21187 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21187 : Upper (D 6) (R 6) [34,72,130,17,320,4] 13 := by
  apply FastRouting.sound _ _ [34,72,130,17,320,4] 13 (by decide) (choices 1) [1,4,32] r21187 c21187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6275
  · exact u6276
  · exact u6277

def b21188 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 196, targets := 1 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 74 134 28 273 33 100 228 356), lower := (rows 35 74 134 28 273 33 64 128 256), losses := [] }

theorem u21188 : Upper (D 6) (R 6) [34,72,130,20,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21189 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 336, targets := 6 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 35 74 134 28 273 36 97 225 353), lower := (rows 35 74 134 28 273 36 64 128 256), losses := [] }

theorem u21189 : Upper (D 6) (R 6) [34,72,130,20,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21190 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 134 28 273 96 101 165 293), lower := (rows 35 74 134 28 273 96 64 128 256), losses := [] }

theorem u21190 : Upper (D 6) (R 6) [34,72,130,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21191 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 196, targets := 32 }], pairs := [(0,2),(0,6),(2,5)], upper := (rows 35 74 134 28 304 33 69 197 325), lower := (rows 35 74 134 28 304 33 64 128 256), losses := [] }

theorem u21191 : Upper (D 6) (R 6) [34,72,130,20,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21192 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 336, targets := 6 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(4,1),(4,2)], upper := (rows 35 74 134 28 304 36 65 193 321), lower := (rows 35 74 134 28 304 36 64 128 256), losses := [] }

theorem u21192 : Upper (D 6) (R 6) [34,72,130,20,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21193 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 134 28 304 96 69 133 261), lower := (rows 35 74 134 28 304 96 64 128 256), losses := [] }

theorem u21193 : Upper (D 6) (R 6) [34,72,130,20,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21194 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 74 134 28 336 33 101 165 293), lower := (rows 35 74 134 28 336 33 64 128 256), losses := [] }

theorem u21194 : Upper (D 6) (R 6) [34,72,130,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21195 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 336, targets := 6 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 35 74 134 28 336 36 97 161 289), lower := (rows 35 74 134 28 336 36 64 128 256), losses := [] }

theorem u21195 : Upper (D 6) (R 6) [34,72,130,20,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21195 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21196 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 134 44 81 33 340 404 276), lower := (rows 35 74 134 44 81 33 64 128 256), losses := [] }

theorem u21196 : Upper (D 6) (R 6) [34,72,130,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21197 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 74 134 44 81 36 337 401 273), lower := (rows 35 74 134 44 81 36 64 128 256), losses := [] }

theorem u21197 : Upper (D 6) (R 6) [34,72,130,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21197 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21198 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 134 44 81 48 325 389 261), lower := (rows 35 74 134 44 81 48 64 128 256), losses := [] }

theorem u21198 : Upper (D 6) (R 6) [34,72,130,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21198 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21199 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 134 44 81 288 85 149 277), lower := (rows 35 74 134 44 81 288 64 128 256), losses := [] }

theorem u21199 : Upper (D 6) (R 6) [34,72,130,36,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21199 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21200 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 134 44 84 33 337 401 273), lower := (rows 35 74 134 44 84 33 64 128 256), losses := [] }

theorem u21200 : Upper (D 6) (R 6) [34,72,130,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21200 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21201 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 134 44 84 48 321 385 257), lower := (rows 35 74 134 44 84 48 64 128 256), losses := [] }

theorem u21201 : Upper (D 6) (R 6) [34,72,130,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21201 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21202 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 134 44 84 288 81 145 273), lower := (rows 35 74 134 44 84 288 64 128 256), losses := [] }

theorem u21202 : Upper (D 6) (R 6) [34,72,130,36,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21202 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21203 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 134 44 273 33 84 212 340), lower := (rows 35 74 134 44 273 33 64 128 256), losses := [] }

theorem u21203 : Upper (D 6) (R 6) [34,72,130,36,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21203 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21204 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 74 134 44 273 36 81 209 337), lower := (rows 35 74 134 44 273 36 64 128 256), losses := [] }

theorem u21204 : Upper (D 6) (R 6) [34,72,130,36,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21205 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 134 44 273 48 69 197 325), lower := (rows 35 74 134 44 273 48 64 128 256), losses := [] }

theorem u21205 : Upper (D 6) (R 6) [34,72,130,36,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21205 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21206 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 134 44 273 96 85 149 277), lower := (rows 35 74 134 44 273 96 64 128 256), losses := [] }

theorem u21206 : Upper (D 6) (R 6) [34,72,130,36,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21207 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 134 44 276 33 81 209 337), lower := (rows 35 74 134 44 276 33 64 128 256), losses := [] }

theorem u21207 : Upper (D 6) (R 6) [34,72,130,36,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21208 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 74 134 44 276 48 65 193 321), lower := (rows 35 74 134 44 276 48 64 128 256), losses := [] }

theorem u21208 : Upper (D 6) (R 6) [34,72,130,36,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21208 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21209 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 134 44 276 96 81 145 273), lower := (rows 35 74 134 44 276 96 64 128 256), losses := [] }

theorem u21209 : Upper (D 6) (R 6) [34,72,130,36,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21210 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 134 44 336 33 85 149 277), lower := (rows 35 74 134 44 336 33 64 128 256), losses := [] }

theorem u21210 : Upper (D 6) (R 6) [34,72,130,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21210 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21211 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 74 134 44 336 36 81 145 273), lower := (rows 35 74 134 44 336 36 64 128 256), losses := [] }

theorem u21211 : Upper (D 6) (R 6) [34,72,130,36,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21212 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 134 44 336 48 69 133 261), lower := (rows 35 74 134 44 336 48 64 128 256), losses := [] }

theorem u21212 : Upper (D 6) (R 6) [34,72,130,36,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21212 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21213 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 134 56 276 33 69 197 325), lower := (rows 35 74 134 56 276 33 64 128 256), losses := [] }

theorem u21213 : Upper (D 6) (R 6) [34,72,130,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21214 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 74 134 56 276 36 65 193 321), lower := (rows 35 74 134 56 276 36 64 128 256), losses := [] }

theorem u21214 : Upper (D 6) (R 6) [34,72,130,48,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21214 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21215 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 134 56 276 96 69 133 261), lower := (rows 35 74 134 56 276 96 64 128 256), losses := [] }

theorem u21215 : Upper (D 6) (R 6) [34,72,130,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21216 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 49, targets := 64 },{ cop := 4, region := 360, targets := 2 }], pairs := [(0,6),(3,1),(4,6)], upper := (rows 35 74 134 265 21 36 112 240 368), lower := (rows 35 74 134 265 21 36 64 128 256), losses := [] }

theorem u21216 : Upper (D 6) (R 6) [34,72,130,257,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21216 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21217 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 49, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 74 134 265 21 48 100 228 356), lower := (rows 35 74 134 265 21 48 64 128 256), losses := [] }

theorem u21217 : Upper (D 6) (R 6) [34,72,130,257,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21217 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21218 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 134 265 21 96 116 180 308), lower := (rows 35 74 134 265 21 96 64 128 256), losses := [] }

theorem u21218 : Upper (D 6) (R 6) [34,72,130,257,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21219 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 212, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 134 265 52 33 84 212 340), lower := (rows 35 74 134 265 52 33 64 128 256), losses := [] }

theorem u21219 : Upper (D 6) (R 6) [34,72,130,257,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21220 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 134 265 52 36 81 209 337), lower := (rows 35 74 134 265 52 36 64 128 256), losses := [] }

theorem u21220 : Upper (D 6) (R 6) [34,72,130,257,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21221 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 134 265 52 48 69 197 325), lower := (rows 35 74 134 265 52 48 64 128 256), losses := [] }

theorem u21221 : Upper (D 6) (R 6) [34,72,130,257,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21221 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21222 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 134 265 52 96 85 149 277), lower := (rows 35 74 134 265 52 96 64 128 256), losses := [] }

theorem u21222 : Upper (D 6) (R 6) [34,72,130,257,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21223 : Route 9 := (fun mask => (mask,id))

def c21223 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21223 : Upper (D 6) (R 6) [34,72,130,257,65,4] 13 := by
  apply FastRouting.sound _ _ [34,72,130,257,65,4] 13 (by decide) (choices 1) [4,16,32] r21223 c21223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6278
  · exact u6279
  · exact u6280

def b21224 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 74 134 265 81 48 100 164 292), lower := (rows 35 74 134 265 81 48 64 128 256), losses := [] }

theorem u21224 : Upper (D 6) (R 6) [34,72,130,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21224 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21225 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 212, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 134 265 84 33 116 180 308), lower := (rows 35 74 134 265 84 33 64 128 256), losses := [] }

theorem u21225 : Upper (D 6) (R 6) [34,72,130,257,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21225 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21226 : Route 9 := (fun mask => (mask,id))

def c21226 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21226 : Upper (D 6) (R 6) [34,72,130,257,68,4] 13 := by
  apply FastRouting.sound _ _ [34,72,130,257,68,4] 13 (by decide) (choices 1) [1,16,32] r21226 c21226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6281
  · exact u6282
  · exact u6283

def b21227 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 74 134 265 84 48 101 165 293), lower := (rows 35 74 134 265 84 48 64 128 256), losses := [] }

theorem u21227 : Upper (D 6) (R 6) [34,72,130,257,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21227 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21228 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 212, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 134 265 112 33 84 148 276), lower := (rows 35 74 134 265 112 33 64 128 256), losses := [] }

theorem u21228 : Upper (D 6) (R 6) [34,72,130,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21228 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21229 : Route 9 := (fun mask => (mask,id))

def c21229 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21229 : Upper (D 6) (R 6) [34,72,130,257,96,4] 13 := by
  apply FastRouting.sound _ _ [34,72,130,257,96,4] 13 (by decide) (choices 1) [1,4,16] r21229 c21229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6284
  · exact u6285
  · exact u6286

def b21230 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 134 265 112 48 69 133 261), lower := (rows 35 74 134 265 112 48 64 128 256), losses := [] }

theorem u21230 : Upper (D 6) (R 6) [34,72,130,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21230 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21231 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 2, region := 49, targets := 64 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 74 134 268 21 33 112 240 368), lower := (rows 35 74 134 268 21 33 64 128 256), losses := [] }

theorem u21231 : Upper (D 6) (R 6) [34,72,130,260,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21231 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21232 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 49, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 74 134 268 21 48 97 225 353), lower := (rows 35 74 134 268 21 48 64 128 256), losses := [] }

theorem u21232 : Upper (D 6) (R 6) [34,72,130,260,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21232 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21233 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 134 268 21 96 113 177 305), lower := (rows 35 74 134 268 21 96 64 128 256), losses := [] }

theorem u21233 : Upper (D 6) (R 6) [34,72,130,260,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21234 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 2, region := 49, targets := 64 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 74 134 268 52 33 81 209 337), lower := (rows 35 74 134 268 52 33 64 128 256), losses := [] }

theorem u21234 : Upper (D 6) (R 6) [34,72,130,260,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21235 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 134 268 52 48 65 193 321), lower := (rows 35 74 134 268 52 48 64 128 256), losses := [] }

theorem u21235 : Upper (D 6) (R 6) [34,72,130,260,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21235 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21236 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 134 268 52 96 81 145 273), lower := (rows 35 74 134 268 52 96 64 128 256), losses := [] }

theorem u21236 : Upper (D 6) (R 6) [34,72,130,260,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21237 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 74 134 268 81 33 116 180 308), lower := (rows 35 74 134 268 81 33 64 128 256), losses := [] }

theorem u21237 : Upper (D 6) (R 6) [34,72,130,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21237 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21238 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 35 74 134 268 81 36 113 177 305), lower := (rows 35 74 134 268 81 36 64 128 256), losses := [] }

theorem u21238 : Upper (D 6) (R 6) [34,72,130,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21239 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 74 134 268 81 48 101 165 293), lower := (rows 35 74 134 268 81 48 64 128 256), losses := [] }

theorem u21239 : Upper (D 6) (R 6) [34,72,130,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21239 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u21239
end Delivery.IrregularNine14.P06
