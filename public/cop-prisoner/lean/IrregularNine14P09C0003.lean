import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0000

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b180 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 302, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,6),(1,7),(2,6),(3,6)], upper := (rows 97 38 140 280 145 33 320 192 258), lower := (rows 97 38 140 280 145 33 320 192 256), losses := [] }

theorem u180 : Upper (D 9) (R 9) [96,36,136,272,129,1,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b180 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b181 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 306, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 97 38 140 328 400 48 65 129 258), lower := (rows 97 38 140 328 400 48 65 129 256), losses := [] }

theorem u181 : Upper (D 9) (R 9) [96,36,136,320,384,16,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b181 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b182 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 182, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 97 38 140 328 400 48 65 130 257), lower := (rows 97 38 140 328 400 48 65 130 256), losses := [] }

theorem u182 : Upper (D 9) (R 9) [96,36,136,320,384,16,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b182 [(5,4),(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b183 : PairBound 9 := { available := 16, camps := [{ cop := 5, region := 207, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 38 196 137 280 288 65 130 272), lower := (rows 97 38 196 137 280 288 65 130 256), losses := [] }

theorem u183 : Upper (D 9) (R 9) [96,36,192,129,264,256,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b183 [(7,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b184 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 290, targets := 65 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(1,7)], upper := (rows 97 38 196 137 280 288 65 144 258), lower := (rows 97 38 196 137 280 288 65 144 256), losses := [] }

theorem u184 : Upper (D 9) (R 9) [96,36,192,129,264,256,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b184 [(7,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b185 : PairBound 9 := { available := 16, camps := [{ cop := 5, region := 207, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 38 196 138 273 288 65 136 272), lower := (rows 97 38 196 138 273 288 65 136 256), losses := [] }

theorem u185 : Upper (D 9) (R 9) [96,36,192,130,257,256,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b185 [(7,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b186 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 298, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 97 38 196 138 273 288 65 144 264), lower := (rows 97 38 196 138 273 288 65 144 256), losses := [] }

theorem u186 : Upper (D 9) (R 9) [96,36,192,130,257,256,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b186 [(7,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b187 : PairBound 9 := { available := 16, camps := [{ cop := 2, region := 314, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6),(4,0)], upper := (rows 97 38 196 138 280 288 65 129 272), lower := (rows 97 38 196 138 280 288 65 129 256), losses := [] }

theorem u187 : Upper (D 9) (R 9) [96,36,192,130,264,256,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b187 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b188 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 1, region := 65, targets := 256 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(4,7)], upper := (rows 97 38 196 138 280 288 65 144 257), lower := (rows 97 38 196 138 280 288 65 144 256), losses := [] }

theorem u188 : Upper (D 9) (R 9) [96,36,192,130,264,256,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b188 [(7,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b189 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 314, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6),(4,0)], upper := (rows 97 38 196 152 274 288 65 129 264), lower := (rows 97 38 196 152 274 288 65 129 256), losses := [] }

theorem u189 : Upper (D 9) (R 9) [96,36,192,144,258,256,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b189 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b190 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 4, region := 136, targets := 1 }], pairs := [(0,7),(1,7),(3,0),(4,7)], upper := (rows 97 38 196 152 274 288 65 136 257), lower := (rows 97 38 196 152 274 288 65 136 256), losses := [] }

theorem u190 : Upper (D 9) (R 9) [96,36,192,144,258,256,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b190 [(7,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b191 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 0, region := 488, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,8)], upper := (rows 7 11 21 104 176 288 192 448 320), lower := (rows 7 11 21 104 176 288 192 128 256), losses := [] }

theorem u191 : Upper (D 9) (R 9) [6,9,17,96,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b191 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b192 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 151, targets := 256 },{ cop := 0, region := 488, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 7 11 21 104 176 288 320 192 448), lower := (rows 7 11 21 104 176 288 320 128 256), losses := [] }

theorem u192 : Upper (D 9) (R 9) [6,9,17,96,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b192 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b193 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 407, targets := 64 },{ cop := 4, region := 111, targets := 256 }], pairs := [(0,6),(0,8),(1,6),(2,6),(4,6)], upper := (rows 7 11 21 104 400 96 192 416 288), lower := (rows 7 11 21 104 400 96 192 128 256), losses := [] }

theorem u193 : Upper (D 9) (R 9) [6,9,17,96,384,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b193 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r194 : Route 9 := (fun mask => (mask,id))

def c194 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u194 : Upper (D 9) (R 9) [6,9,17,96,384,128,256] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96,384,128,256] 13 (by decide) (choices 1) [32,64] r194 c194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u0
  · exact u1

def b195 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 11 37 88 176 288 192 448 320), lower := (rows 7 11 37 88 176 288 192 128 256), losses := [] }

theorem u195 : Upper (D 9) (R 9) [6,9,33,80,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b195 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b196 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 328, targets := 32 }], pairs := [(0,6),(1,6),(3,0),(3,5),(4,0)], upper := (rows 7 11 37 88 176 288 320 192 448), lower := (rows 7 11 37 88 176 288 320 128 256), losses := [{ target := 6, region := (rows 11 10 12 8 16 352 0 128 256), good := (rows 7 15 37 63 176 288 288 128 288) }] }

theorem u196 : Upper (D 9) (R 9) [6,9,33,80,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b196 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b197 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 295, targets := 64 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 7 11 37 200 112 288 80 384 384), lower := (rows 7 11 37 200 112 288 80 128 256), losses := [] }

theorem u197 : Upper (D 9) (R 9) [6,9,33,192,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b197 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b198 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 311, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 7 11 37 200 112 288 192 400 272), lower := (rows 7 11 37 200 112 288 192 128 256), losses := [] }

theorem u198 : Upper (D 9) (R 9) [6,9,33,192,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b198 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b199 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 143, targets := 256 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,8)], upper := (rows 7 11 37 200 112 288 320 144 400), lower := (rows 7 11 37 200 112 288 320 128 256), losses := [] }

theorem u199 : Upper (D 9) (R 9) [6,9,33,192,96,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b199 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b200 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 6, region := 408, targets := 32 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 7 11 37 200 336 48 96 384 384), lower := (rows 7 11 37 200 336 48 96 128 256), losses := [] }

theorem u200 : Upper (D 9) (R 9) [6,9,33,192,320,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b200 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b201 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 37 200 336 48 192 416 288), lower := (rows 7 11 37 200 336 48 192 128 256), losses := [] }

theorem u201 : Upper (D 9) (R 9) [6,9,33,192,320,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b201 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b202 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 11 37 200 336 48 320 160 416), lower := (rows 7 11 37 200 336 48 320 128 256), losses := [] }

theorem u202 : Upper (D 9) (R 9) [6,9,33,192,320,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b202 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b203 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 295, targets := 64 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 7 11 37 200 336 288 80 160 416), lower := (rows 7 11 37 200 336 288 80 128 256), losses := [] }

theorem u203 : Upper (D 9) (R 9) [6,9,33,192,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b203 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b204 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 6, region := 408, targets := 32 },{ cop := 4, region := 136, targets := 256 }], pairs := [(3,0),(3,5),(3,8),(4,0),(4,5)], upper := (rows 7 11 37 200 336 288 96 144 400), lower := (rows 7 11 37 200 336 288 96 128 256), losses := [] }

theorem u204 : Upper (D 9) (R 9) [6,9,33,192,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b204 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b205 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 311, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 7 11 37 200 336 288 192 176 304), lower := (rows 7 11 37 200 336 288 192 128 256), losses := [] }

theorem u205 : Upper (D 9) (R 9) [6,9,33,192,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b205 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b206 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 364, targets := 1 },{ cop := 0, region := 464, targets := 32 },{ cop := 6, region := 296, targets := 128 }], pairs := [(0,8),(2,0),(3,0),(3,7),(4,5)], upper := (rows 7 11 52 104 145 288 192 448 320), lower := (rows 7 11 52 104 145 288 192 128 256), losses := [{ target := 8, region := (rows 5 7 4 12 16 32 208 128 0), good := (rows 15 11 127 104 211 32 192 192 0) }] }

theorem u206 : Upper (D 9) (R 9) [6,9,48,96,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b206 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b207 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 151, targets := 256 },{ cop := 4, region := 356, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(4,8)], upper := (rows 7 11 52 104 145 288 320 192 448), lower := (rows 7 11 52 104 145 288 320 128 256), losses := [] }

theorem u207 : Upper (D 9) (R 9) [6,9,48,96,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b207 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b208 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 75, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 7 11 52 104 208 288 65 384 384), lower := (rows 7 11 52 104 208 288 65 128 256), losses := [] }

theorem u208 : Upper (D 9) (R 9) [6,9,48,96,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b208 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b209 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,0)], upper := (rows 7 11 52 104 208 288 192 385 257), lower := (rows 7 11 52 104 208 288 192 128 256), losses := [] }

theorem u209 : Upper (D 9) (R 9) [6,9,48,96,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b209 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b210 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 151, targets := 256 },{ cop := 5, region := 72, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 7 11 52 104 208 288 320 129 385), lower := (rows 7 11 52 104 208 288 320 128 256), losses := [] }

theorem u210 : Upper (D 9) (R 9) [6,9,48,96,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b210 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b211 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 5, region := 468, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,8)], upper := (rows 7 11 52 104 400 33 192 448 320), lower := (rows 7 11 52 104 400 33 192 128 256), losses := [] }

theorem u211 : Upper (D 9) (R 9) [6,9,48,96,384,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b211 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b212 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 428, targets := 1 },{ cop := 4, region := 394, targets := 32 },{ cop := 4, region := 420, targets := 64 }], pairs := [(1,5),(2,0),(2,6),(3,0),(3,5)], upper := (rows 7 11 52 200 81 288 96 384 384), lower := (rows 7 11 52 200 81 288 96 128 256), losses := [] }

theorem u212 : Upper (D 9) (R 9) [6,9,48,192,65,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b212 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b213 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 311, targets := 128 },{ cop := 4, region := 292, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,7),(4,7)], upper := (rows 7 11 52 200 81 288 192 416 288), lower := (rows 7 11 52 200 81 288 192 128 256), losses := [] }

theorem u213 : Upper (D 9) (R 9) [6,9,48,192,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b213 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b214 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 428, targets := 1 },{ cop := 4, region := 420, targets := 64 }], pairs := [(0,7),(1,7),(2,0),(2,6),(3,0)], upper := (rows 7 11 52 200 81 288 320 160 416), lower := (rows 7 11 52 200 81 288 320 128 256), losses := [{ target := 7, region := (rows 11 10 28 8 24 352 352 0 256), good := (rows 7 31 116 127 117 352 352 0 352) }] }

theorem u214 : Upper (D 9) (R 9) [6,9,48,192,65,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b214 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b215 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 400, targets := 96 },{ cop := 4, region := 236, targets := 1 },{ cop := 4, region := 100, targets := 128 }], pairs := [(2,0),(2,7),(3,0),(4,5),(4,6)], upper := (rows 7 11 52 200 273 96 96 384 384), lower := (rows 7 11 52 200 273 96 96 128 256), losses := [] }

theorem u215 : Upper (D 9) (R 9) [6,9,48,192,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b215 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b216 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 311, targets := 128 },{ cop := 4, region := 228, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,7),(4,7)], upper := (rows 7 11 52 200 273 96 192 416 288), lower := (rows 7 11 52 200 273 96 192 128 256), losses := [] }

theorem u216 : Upper (D 9) (R 9) [6,9,48,192,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b216 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b217 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 236, targets := 1 },{ cop := 4, region := 100, targets := 128 },{ cop := 5, region := 136, targets := 256 }], pairs := [(2,0),(2,7),(3,0),(3,8),(4,6)], upper := (rows 7 11 52 200 273 96 320 160 416), lower := (rows 7 11 52 200 273 96 320 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 17 32 0 164 292), good := (rows 407 27 436 136 273 416 256 128 256) }] }

theorem u217 : Upper (D 9) (R 9) [6,9,48,192,257,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b217 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b218 : PairBound 9 := { available := 384, camps := [{ cop := 5, region := 476, targets := 1 },{ cop := 6, region := 408, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0),(4,5)], upper := (rows 7 11 52 200 336 33 96 384 384), lower := (rows 7 11 52 200 336 33 96 128 256), losses := [] }

theorem u218 : Upper (D 9) (R 9) [6,9,48,192,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b218 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b219 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 311, targets := 128 },{ cop := 5, region := 468, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,7),(4,7)], upper := (rows 7 11 52 200 336 33 192 416 288), lower := (rows 7 11 52 200 336 33 192 128 256), losses := [] }

theorem u219 : Upper (D 9) (R 9) [6,9,48,192,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b219 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b220 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 175, targets := 256 },{ cop := 5, region := 468, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,8)], upper := (rows 7 11 52 200 336 33 320 160 416), lower := (rows 7 11 52 200 336 33 320 128 256), losses := [] }

theorem u220 : Upper (D 9) (R 9) [6,9,48,192,320,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b220 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b221 : PairBound 9 := { available := 288, camps := [{ cop := 6, region := 444, targets := 1 },{ cop := 4, region := 164, targets := 64 }], pairs := [(2,0),(2,6),(3,0),(4,0),(4,7)], upper := (rows 7 11 52 200 336 160 65 416 288), lower := (rows 7 11 52 200 336 160 65 128 256), losses := [{ target := 7, region := (rows 1 2 4 8 17 32 67 0 292), good := (rows 343 91 308 72 336 288 81 0 256) }] }

theorem u221 : Upper (D 9) (R 9) [6,9,48,192,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b221 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b222 : PairBound 9 := { available := 257, camps := [{ cop := 5, region := 72, targets := 257 }], pairs := [(0,8),(1,8),(3,0),(3,8),(4,7)], upper := (rows 7 11 52 200 336 160 96 385 257), lower := (rows 7 11 52 200 336 160 96 128 256), losses := [{ target := 7, region := (rows 1 2 4 8 17 32 100 0 259), good := (rows 343 283 116 72 336 96 96 0 256) },{ target := 8, region := (rows 5 6 4 168 16 168 238 128 0), good := (rows 71 107 127 232 80 232 104 232 0) }] }

theorem u222 : Upper (D 9) (R 9) [6,9,48,192,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b222 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b223 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 175, targets := 256 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 7 11 52 200 336 160 320 161 289), lower := (rows 7 11 52 200 336 160 320 128 256), losses := [] }

theorem u223 : Upper (D 9) (R 9) [6,9,48,192,320,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b223 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b224 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 364, targets := 1 },{ cop := 0, region := 464, targets := 32 },{ cop := 6, region := 292, targets := 128 }], pairs := [(1,7),(2,0),(2,7),(3,0),(4,5)], upper := (rows 7 11 100 56 145 288 192 448 320), lower := (rows 7 11 100 56 145 288 192 128 256), losses := [{ target := 7, region := (rows 1 18 68 24 16 357 64 0 324), good := (rows 295 43 356 58 59 288 356 0 288) }] }

theorem u224 : Upper (D 9) (R 9) [6,9,96,48,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b224 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b225 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 155, targets := 256 },{ cop := 4, region := 356, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(3,8),(4,8)], upper := (rows 7 11 100 56 145 288 320 192 448), lower := (rows 7 11 100 56 145 288 320 128 256), losses := [] }

theorem u225 : Upper (D 9) (R 9) [6,9,96,48,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b225 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b226 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 11 100 56 208 288 65 384 384), lower := (rows 7 11 100 56 208 288 65 128 256), losses := [] }

theorem u226 : Upper (D 9) (R 9) [6,9,96,48,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b226 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b227 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,0)], upper := (rows 7 11 100 56 208 288 192 385 257), lower := (rows 7 11 100 56 208 288 192 128 256), losses := [] }

theorem u227 : Upper (D 9) (R 9) [6,9,96,48,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b227 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b228 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 155, targets := 256 },{ cop := 5, region := 68, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(3,8),(4,8)], upper := (rows 7 11 100 56 208 288 320 129 385), lower := (rows 7 11 100 56 208 288 320 128 256), losses := [] }

theorem u228 : Upper (D 9) (R 9) [6,9,96,48,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b228 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b229 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 5, region := 452, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,8)], upper := (rows 7 11 100 56 400 33 192 448 320), lower := (rows 7 11 100 56 400 33 192 128 256), losses := [] }

theorem u229 : Upper (D 9) (R 9) [6,9,96,48,384,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b229 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b230 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 460, targets := 1 },{ cop := 4, region := 458, targets := 32 },{ cop := 6, region := 292, targets := 128 }], pairs := [(1,5),(2,0),(2,7),(3,0),(3,5)], upper := (rows 7 11 100 152 49 288 192 448 320), lower := (rows 7 11 100 152 49 288 192 128 256), losses := [] }

theorem u230 : Upper (D 9) (R 9) [6,9,96,144,33,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b230 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b231 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 155, targets := 256 },{ cop := 4, region := 452, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(3,8),(4,8)], upper := (rows 7 11 100 152 49 288 320 192 448), lower := (rows 7 11 100 152 49 288 320 128 256), losses := [] }

theorem u231 : Upper (D 9) (R 9) [6,9,96,144,33,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b231 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b232 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 3, region := 103, targets := 256 }], pairs := [(0,6),(0,8),(1,6),(3,6),(4,6)], upper := (rows 7 11 100 152 273 96 192 416 288), lower := (rows 7 11 100 152 273 96 192 128 256), losses := [] }

theorem u232 : Upper (D 9) (R 9) [6,9,96,144,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b232 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b233 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 4, region := 100, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 11 100 152 273 96 320 160 416), lower := (rows 7 11 100 152 273 96 320 128 256), losses := [] }

theorem u233 : Upper (D 9) (R 9) [6,9,96,144,257,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b233 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b234 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 236, targets := 1 },{ cop := 5, region := 324, targets := 128 },{ cop := 6, region := 164, targets := 256 }], pairs := [(2,0),(2,7),(2,8),(3,0),(4,7)], upper := (rows 7 11 100 152 273 160 320 224 352), lower := (rows 7 11 100 152 273 160 320 128 256), losses := [{ target := 7, region := (rows 1 2 36 8 17 32 373 0 292), good := (rows 343 91 356 88 337 356 320 0 320) }] }

theorem u234 : Upper (D 9) (R 9) [6,9,96,144,257,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b234 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b235 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 5, region := 476, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,0)], upper := (rows 7 11 100 152 304 33 192 448 320), lower := (rows 7 11 100 152 304 33 192 128 256), losses := [] }

theorem u235 : Upper (D 9) (R 9) [6,9,96,144,288,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b235 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b236 : PairBound 9 := { available := 192, camps := [{ cop := 5, region := 476, targets := 1 },{ cop := 4, region := 200, targets := 32 },{ cop := 4, region := 68, targets := 128 }], pairs := [(2,0),(2,7),(3,0),(3,5),(4,0)], upper := (rows 7 11 100 152 304 33 320 192 448), lower := (rows 7 11 100 152 304 33 320 128 256), losses := [] }

theorem u236 : Upper (D 9) (R 9) [6,9,96,144,288,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b236 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b237 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 6, region := 444, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,0)], upper := (rows 7 11 100 152 304 160 65 448 320), lower := (rows 7 11 100 152 304 160 65 128 256), losses := [] }

theorem u237 : Upper (D 9) (R 9) [6,9,96,144,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b237 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r238 : Route 9 := (fun mask => (mask,id))

def c238 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u238 : Upper (D 9) (R 9) [6,9,96,144,288,128,256] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,288,128,256] 13 (by decide) (choices 1) [1,64] r238 c238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2
  · exact u3

def b239 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 87, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 7 11 100 168 145 288 80 448 320), lower := (rows 7 11 100 168 145 288 80 128 256), losses := [] }

theorem u239 : Upper (D 9) (R 9) [6,9,96,160,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b239 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u239
end Delivery.IrregularNine14.P09
