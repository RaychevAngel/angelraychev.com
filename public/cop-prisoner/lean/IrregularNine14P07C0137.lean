import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0010

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8220 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 37 98 262 88 146 33 72 129 385), lower := (rows 37 98 262 88 146 33 72 128 256), losses := [] }

theorem u8220 : Upper (D 7) (R 7) [36,96,258,80,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8220 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8221 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(3,0)], upper := (rows 37 98 262 88 146 33 192 137 265), lower := (rows 37 98 262 88 146 33 192 128 256), losses := [] }

theorem u8221 : Upper (D 7) (R 7) [36,96,258,80,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8221 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8222 : Route 9 := (fun mask => (mask,id))

def c8222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8222 : Upper (D 7) (R 7) [36,96,258,80,130,128,1] 13 := by
  apply FastRouting.sound _ _ [36,96,258,80,130,128,1] 13 (by decide) (choices 1) [1,8] r8222 c8222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u656
  · exact u657

def b8223 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 262 88 146 160 72 129 257), lower := (rows 37 98 262 88 146 160 72 128 256), losses := [] }

theorem u8223 : Upper (D 7) (R 7) [36,96,258,80,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8223 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8224 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 262 137 146 40 65 208 336), lower := (rows 37 98 262 137 146 40 65 128 256), losses := [] }

theorem u8224 : Upper (D 7) (R 7) [36,96,258,129,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8224 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8225 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 261, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 37 98 262 137 146 40 80 193 321), lower := (rows 37 98 262 137 146 40 80 128 256), losses := [] }

theorem u8225 : Upper (D 7) (R 7) [36,96,258,129,130,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8225 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8226 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 200, targets := 34 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7),(3,1),(3,5)], upper := (rows 37 98 262 137 146 48 65 200 328), lower := (rows 37 98 262 137 146 48 65 128 256), losses := [] }

theorem u8226 : Upper (D 7) (R 7) [36,96,258,129,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8226 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8227 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 200, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 37 98 262 137 146 48 72 193 321), lower := (rows 37 98 262 137 146 48 72 128 256), losses := [] }

theorem u8227 : Upper (D 7) (R 7) [36,96,258,129,130,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8227 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8228 : PairBound 9 := { available := 24, camps := [{ cop := 8, region := 103, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 37 98 262 137 208 33 66 152 280), lower := (rows 37 98 262 137 208 33 66 128 256), losses := [] }

theorem u8228 : Upper (D 7) (R 7) [36,96,258,129,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8229 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 262 137 208 33 72 146 274), lower := (rows 37 98 262 137 208 33 72 128 256), losses := [] }

theorem u8229 : Upper (D 7) (R 7) [36,96,258,129,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8229 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8230 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 262 137 208 33 80 138 266), lower := (rows 37 98 262 137 208 33 80 128 256), losses := [] }

theorem u8230 : Upper (D 7) (R 7) [36,96,258,129,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8230 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8231 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 262 137 208 40 65 146 274), lower := (rows 37 98 262 137 208 40 65 128 256), losses := [] }

theorem u8231 : Upper (D 7) (R 7) [36,96,258,129,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8231 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8232 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 114, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 262 137 208 40 66 145 273), lower := (rows 37 98 262 137 208 40 66 128 256), losses := [] }

theorem u8232 : Upper (D 7) (R 7) [36,96,258,129,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8232 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8233 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 261, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 262 137 208 40 80 131 259), lower := (rows 37 98 262 137 208 40 80 128 256), losses := [] }

theorem u8233 : Upper (D 7) (R 7) [36,96,258,129,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8233 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8234 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 262 138 208 33 65 152 280), lower := (rows 37 98 262 138 208 33 65 128 256), losses := [] }

theorem u8234 : Upper (D 7) (R 7) [36,96,258,130,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8235 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7)], upper := (rows 37 98 262 138 208 33 72 145 273), lower := (rows 37 98 262 138 208 33 72 128 256), losses := [] }

theorem u8235 : Upper (D 7) (R 7) [36,96,258,130,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8235 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8236 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 262 138 208 33 80 137 265), lower := (rows 37 98 262 138 208 33 80 128 256), losses := [] }

theorem u8236 : Upper (D 7) (R 7) [36,96,258,130,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8236 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8237 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 90, targets := 128 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,7),(2,5),(3,7),(4,7)], upper := (rows 37 98 268 11 81 160 66 144 400), lower := (rows 37 98 268 11 81 160 66 128 256), losses := [] }

theorem u8237 : Upper (D 7) (R 7) [36,96,264,3,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8237 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8238 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 90, targets := 128 }], pairs := [(1,7),(3,7),(4,7)], upper := (rows 37 98 268 11 81 160 80 130 386), lower := (rows 37 98 268 11 81 160 80 128 256), losses := [] }

theorem u8238 : Upper (D 7) (R 7) [36,96,264,3,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8238 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8239 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 268 11 81 160 192 146 274), lower := (rows 37 98 268 11 81 160 192 128 256), losses := [] }

theorem u8239 : Upper (D 7) (R 7) [36,96,264,3,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8240 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,7),(2,5),(3,7),(4,5)], upper := (rows 37 98 268 11 145 160 66 208 336), lower := (rows 37 98 268 11 145 160 66 128 256), losses := [] }

theorem u8240 : Upper (D 7) (R 7) [36,96,264,3,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8240 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8241 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 268 11 145 160 80 194 322), lower := (rows 37 98 268 11 145 160 80 128 256), losses := [] }

theorem u8241 : Upper (D 7) (R 7) [36,96,264,3,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8241 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8242 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,7),(2,5),(3,7),(4,5)], upper := (rows 37 98 268 11 146 160 65 208 336), lower := (rows 37 98 268 11 146 160 65 128 256), losses := [] }

theorem u8242 : Upper (D 7) (R 7) [36,96,264,3,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8243 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 268 11 146 160 80 193 321), lower := (rows 37 98 268 11 146 160 80 128 256), losses := [] }

theorem u8243 : Upper (D 7) (R 7) [36,96,264,3,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8243 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8244 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,7),(2,5),(3,7),(4,5)], upper := (rows 37 98 268 11 208 160 65 146 274), lower := (rows 37 98 268 11 208 160 65 128 256), losses := [] }

theorem u8244 : Upper (D 7) (R 7) [36,96,264,3,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8245 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,7),(2,5),(3,7),(4,5)], upper := (rows 37 98 268 11 208 160 66 145 273), lower := (rows 37 98 268 11 208 160 66 128 256), losses := [] }

theorem u8245 : Upper (D 7) (R 7) [36,96,264,3,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8246 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 268 11 208 160 80 131 259), lower := (rows 37 98 268 11 208 160 80 128 256), losses := [] }

theorem u8246 : Upper (D 7) (R 7) [36,96,264,3,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8246 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8247 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 178, targets := 1 },{ cop := 0, region := 66, targets := 128 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 37 98 268 25 146 160 65 194 322), lower := (rows 37 98 268 25 146 160 65 128 256), losses := [] }

theorem u8247 : Upper (D 7) (R 7) [36,96,264,17,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8248 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 82, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,5),(4,0)], upper := (rows 37 98 268 25 146 160 66 193 321), lower := (rows 37 98 268 25 146 160 66 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 82 136 264), good := (rows 5 66 396 477 210 128 66 128 256) }] }

theorem u8248 : Upper (D 7) (R 7) [36,96,264,17,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8249 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 6, region := 178, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 37 98 268 25 208 34 65 130 386), lower := (rows 37 98 268 25 208 34 65 128 256), losses := [] }

theorem u8249 : Upper (D 7) (R 7) [36,96,264,17,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8250 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 268 25 208 34 66 129 385), lower := (rows 37 98 268 25 208 34 66 128 256), losses := [] }

theorem u8250 : Upper (D 7) (R 7) [36,96,264,17,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8251 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 98 268 25 208 34 192 131 259), lower := (rows 37 98 268 25 208 34 192 128 256), losses := [] }

theorem u8251 : Upper (D 7) (R 7) [36,96,264,17,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8251 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8252 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 178, targets := 1 },{ cop := 0, region := 66, targets := 128 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 37 98 268 25 208 160 65 130 258), lower := (rows 37 98 268 25 208 160 65 128 256), losses := [] }

theorem u8252 : Upper (D 7) (R 7) [36,96,264,17,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8253 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 82, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(4,0)], upper := (rows 37 98 268 25 208 160 66 131 259), lower := (rows 37 98 268 25 208 160 66 128 256), losses := [{ target := 7, region := (rows 1 35 12 8 16 32 107 0 265), good := (rows 359 98 332 351 80 98 66 0 256) }] }

theorem u8253 : Upper (D 7) (R 7) [36,96,264,17,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8254 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 90, targets := 128 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(1,7),(3,7),(4,7)], upper := (rows 37 98 268 26 81 160 65 130 386), lower := (rows 37 98 268 26 81 160 65 128 256), losses := [] }

theorem u8254 : Upper (D 7) (R 7) [36,96,264,18,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8254 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8255 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 421, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 268 26 81 160 66 129 385), lower := (rows 37 98 268 26 81 160 66 128 256), losses := [] }

theorem u8255 : Upper (D 7) (R 7) [36,96,264,18,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8256 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 268 26 81 160 192 131 259), lower := (rows 37 98 268 26 81 160 192 128 256), losses := [] }

theorem u8256 : Upper (D 7) (R 7) [36,96,264,18,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8256 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8257 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 66, targets := 128 },{ cop := 6, region := 162, targets := 1 }], pairs := [(1,0),(1,7),(2,0),(2,5)], upper := (rows 37 98 268 26 145 160 65 194 322), lower := (rows 37 98 268 26 145 160 65 128 256), losses := [{ target := 0, region := (rows 0 66 12 8 16 250 64 194 322), good := (rows 36 482 300 446 176 160 482 160 256) },{ target := 5, region := (rows 1 2 12 8 16 0 81 138 266), good := (rows 69 450 396 478 209 128 65 128 256) }] }

theorem u8257 : Upper (D 7) (R 7) [36,96,264,18,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8258 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 106, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 37 98 268 26 145 160 66 193 321), lower := (rows 37 98 268 26 145 160 66 128 256), losses := [{ target := 7, region := (rows 1 35 28 24 16 32 123 0 273), good := (rows 359 98 332 350 351 98 66 0 256) }] }

theorem u8258 : Upper (D 7) (R 7) [36,96,264,18,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8258 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8259 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 90, targets := 128 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,7),(2,5),(3,7),(4,7)], upper := (rows 37 98 268 73 19 160 66 144 400), lower := (rows 37 98 268 73 19 160 66 128 256), losses := [] }

theorem u8259 : Upper (D 7) (R 7) [36,96,264,65,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8260 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 90, targets := 128 }], pairs := [(1,7),(3,7),(4,7)], upper := (rows 37 98 268 73 19 160 80 130 386), lower := (rows 37 98 268 73 19 160 80 128 256), losses := [] }

theorem u8260 : Upper (D 7) (R 7) [36,96,264,65,3,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8260 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8261 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 268 73 19 160 192 146 274), lower := (rows 37 98 268 73 19 160 192 128 256), losses := [] }

theorem u8261 : Upper (D 7) (R 7) [36,96,264,65,3,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8262 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 404, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(4,1)], upper := (rows 37 98 268 73 145 34 66 144 400), lower := (rows 37 98 268 73 145 34 66 128 256), losses := [] }

theorem u8262 : Upper (D 7) (R 7) [36,96,264,65,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8263 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 422, targets := 1 },{ cop := 4, region := 72, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 37 98 268 73 145 34 80 130 386), lower := (rows 37 98 268 73 145 34 80 128 256), losses := [] }

theorem u8263 : Upper (D 7) (R 7) [36,96,264,65,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8263 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8264 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 34, targets := 129 },{ cop := 4, region := 72, targets := 34 }], pairs := [(1,0),(1,7),(3,1),(3,5)], upper := (rows 37 98 268 73 145 34 192 146 274), lower := (rows 37 98 268 73 145 34 192 128 256), losses := [] }

theorem u8264 : Upper (D 7) (R 7) [36,96,264,65,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8264 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8265 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 0, region := 66, targets := 1 }], pairs := [(1,0),(1,7),(3,7)], upper := (rows 37 98 268 73 145 48 66 130 386), lower := (rows 37 98 268 73 145 48 66 128 256), losses := [] }

theorem u8265 : Upper (D 7) (R 7) [36,96,264,65,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8265 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8266 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 268 73 145 48 192 130 258), lower := (rows 37 98 268 73 145 48 192 128 256), losses := [] }

theorem u8266 : Upper (D 7) (R 7) [36,96,264,65,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8266 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8267 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 0, region := 66, targets := 1 }], pairs := [(1,0),(1,7),(2,7),(3,7)], upper := (rows 37 98 268 73 145 160 66 146 274), lower := (rows 37 98 268 73 145 160 66 128 256), losses := [{ target := 7, region := (rows 1 35 20 25 16 32 123 0 272), good := (rows 111 98 332 75 351 98 66 0 256) }] }

theorem u8267 : Upper (D 7) (R 7) [36,96,264,65,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8268 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 268 73 145 160 80 130 258), lower := (rows 37 98 268 73 145 160 80 128 256), losses := [] }

theorem u8268 : Upper (D 7) (R 7) [36,96,264,65,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8268 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8269 : PairBound 9 := { available := 144, camps := [{ cop := 8, region := 111, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 98 268 73 146 34 65 144 400), lower := (rows 37 98 268 73 146 34 65 128 256), losses := [] }

theorem u8269 : Upper (D 7) (R 7) [36,96,264,65,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8270 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 98 268 73 146 34 80 129 385), lower := (rows 37 98 268 73 146 34 80 128 256), losses := [] }

theorem u8270 : Upper (D 7) (R 7) [36,96,264,65,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8270 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8271 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 34, targets := 129 },{ cop := 6, region := 50, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 37 98 268 73 146 34 192 145 273), lower := (rows 37 98 268 73 146 34 192 128 256), losses := [{ target := 7, region := (rows 5 74 4 8 16 126 64 0 256), good := (rows 37 98 303 107 50 34 98 0 256) }] }

theorem u8271 : Upper (D 7) (R 7) [36,96,264,65,130,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8272 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 37 98 268 73 146 48 65 130 386), lower := (rows 37 98 268 73 146 48 65 128 256), losses := [] }

theorem u8272 : Upper (D 7) (R 7) [36,96,264,65,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8272 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8273 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 98 268 73 146 48 66 129 385), lower := (rows 37 98 268 73 146 48 66 128 256), losses := [] }

theorem u8273 : Upper (D 7) (R 7) [36,96,264,65,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8273 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8274 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 268 73 146 48 192 131 259), lower := (rows 37 98 268 73 146 48 192 128 256), losses := [] }

theorem u8274 : Upper (D 7) (R 7) [36,96,264,65,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8274 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8275 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 438, targets := 1 },{ cop := 6, region := 8, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 37 98 268 73 146 160 65 146 274), lower := (rows 37 98 268 73 146 160 65 128 256), losses := [] }

theorem u8275 : Upper (D 7) (R 7) [36,96,264,65,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8275 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8276 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 5, region := 82, targets := 1 }], pairs := [(1,0),(1,7),(3,7),(4,0)], upper := (rows 37 98 268 73 146 160 66 145 273), lower := (rows 37 98 268 73 146 160 66 128 256), losses := [] }

theorem u8276 : Upper (D 7) (R 7) [36,96,264,65,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8276 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8277 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 268 73 146 160 80 131 259), lower := (rows 37 98 268 73 146 160 80 128 256), losses := [] }

theorem u8277 : Upper (D 7) (R 7) [36,96,264,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8277 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8278 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 3, region := 422, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 37 98 268 88 145 34 65 130 386), lower := (rows 37 98 268 88 145 34 65 128 256), losses := [] }

theorem u8278 : Upper (D 7) (R 7) [36,96,264,80,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8279 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 268 88 145 34 66 129 385), lower := (rows 37 98 268 88 145 34 66 128 256), losses := [] }

theorem u8279 : Upper (D 7) (R 7) [36,96,264,80,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u8279
end Delivery.IrregularNine14.P07
