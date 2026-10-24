import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0012

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9000 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 6, region := 176, targets := 3 }], pairs := [(1,5),(2,5),(4,0),(4,1)], upper := (rows 37 259 14 25 112 160 66 192 448), lower := (rows 37 259 14 25 112 160 66 128 256), losses := [] }

theorem u9000 : Upper (D 7) (R 7) [36,257,10,17,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9001 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 14 25 112 160 192 194 322), lower := (rows 37 259 14 25 112 160 192 128 256), losses := [] }

theorem u9001 : Upper (D 7) (R 7) [36,257,10,17,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9002 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 144, targets := 3 },{ cop := 0, region := 386, targets := 64 },{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7),(1,6),(4,0),(4,1)], upper := (rows 37 259 14 25 208 96 66 160 416), lower := (rows 37 259 14 25 208 96 66 128 256), losses := [] }

theorem u9002 : Upper (D 7) (R 7) [36,257,10,17,192,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9003 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 390, targets := 96 }], pairs := [(1,5),(1,6),(2,5),(2,6)], upper := (rows 37 259 14 25 208 96 96 130 386), lower := (rows 37 259 14 25 208 96 96 128 256), losses := [] }

theorem u9003 : Upper (D 7) (R 7) [36,257,10,17,192,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9004 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 14 25 208 96 192 162 290), lower := (rows 37 259 14 25 208 96 192 128 256), losses := [] }

theorem u9004 : Upper (D 7) (R 7) [36,257,10,17,192,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9004 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9005 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 259 14 73 50 160 80 192 448), lower := (rows 37 259 14 73 50 160 80 128 256), losses := [] }

theorem u9005 : Upper (D 7) (R 7) [36,257,10,65,34,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9005 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9006 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(2,5),(3,1),(3,5),(4,0)], upper := (rows 37 259 14 73 50 160 192 208 336), lower := (rows 37 259 14 73 50 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 240 240 144 272), good := (rows 109 265 12 105 496 224 224 224 256) },{ target := 5, region := (rows 1 2 6 9 16 0 240 144 272), good := (rows 77 271 14 73 470 192 192 192 256) }] }

theorem u9006 : Upper (D 7) (R 7) [36,257,10,65,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9006 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9007 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 92, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 37 259 14 73 82 160 80 160 416), lower := (rows 37 259 14 73 82 160 80 128 256), losses := [] }

theorem u9007 : Upper (D 7) (R 7) [36,257,10,65,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9007 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9008 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 259 14 73 82 160 96 144 400), lower := (rows 37 259 14 73 82 160 96 128 256), losses := [] }

theorem u9008 : Upper (D 7) (R 7) [36,257,10,65,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9008 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9009 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(2,5),(3,1),(3,5),(4,0)], upper := (rows 37 259 14 73 82 160 192 176 304), lower := (rows 37 259 14 73 82 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 240 240 144 272), good := (rows 109 265 12 105 496 224 224 224 256) },{ target := 5, region := (rows 1 2 6 9 16 0 224 128 256), good := (rows 77 271 14 73 86 192 192 192 256) }] }

theorem u9009 : Upper (D 7) (R 7) [36,257,10,65,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9010 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 37 259 14 73 112 160 66 144 400), lower := (rows 37 259 14 73 112 160 66 128 256), losses := [] }

theorem u9010 : Upper (D 7) (R 7) [36,257,10,65,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9011 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 37 259 14 73 112 160 80 130 386), lower := (rows 37 259 14 73 112 160 80 128 256), losses := [] }

theorem u9011 : Upper (D 7) (R 7) [36,257,10,65,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9011 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9012 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 14 73 112 160 192 146 274), lower := (rows 37 259 14 73 112 160 192 128 256), losses := [] }

theorem u9012 : Upper (D 7) (R 7) [36,257,10,65,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9012 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9013 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 259 14 73 146 48 96 192 448), lower := (rows 37 259 14 73 146 48 96 128 256), losses := [] }

theorem u9013 : Upper (D 7) (R 7) [36,257,10,65,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9013 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9014 : Route 9 := (fun mask => (mask,id))

def c9014 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9014 : Upper (D 7) (R 7) [36,257,10,65,130,16,128] 13 := by
  apply FastRouting.sound _ _ [36,257,10,65,130,16,128] 13 (by decide) (choices 1) [32,64] r9014 c9014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u721
  · exact u722

def r9015 : Route 9 := (fun mask => (mask,id))

def c9015 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9015 : Upper (D 7) (R 7) [36,257,10,65,130,128,16] 13 := by
  apply FastRouting.sound _ _ [36,257,10,65,130,128,16] 13 (by decide) (choices 1) [32,64] r9015 c9015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u723
  · exact u724

def b9016 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 259 14 73 146 160 96 208 336), lower := (rows 37 259 14 73 146 160 96 128 256), losses := [] }

theorem u9016 : Upper (D 7) (R 7) [36,257,10,65,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9017 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 37 259 14 73 208 160 66 176 304), lower := (rows 37 259 14 73 208 160 66 128 256), losses := [] }

theorem u9017 : Upper (D 7) (R 7) [36,257,10,65,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9018 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 37 259 14 73 208 160 80 162 290), lower := (rows 37 259 14 73 208 160 80 128 256), losses := [] }

theorem u9018 : Upper (D 7) (R 7) [36,257,10,65,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9018 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9019 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 259 14 73 208 160 96 146 274), lower := (rows 37 259 14 73 208 160 96 128 256), losses := [] }

theorem u9019 : Upper (D 7) (R 7) [36,257,10,65,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9020 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(0,1),(1,7),(2,7),(4,1)], upper := (rows 37 259 14 88 145 160 66 224 352), lower := (rows 37 259 14 88 145 160 66 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 20 252 64 200 328), good := (rows 53 257 445 504 177 160 480 160 256) },{ target := 7, region := (rows 1 19 28 24 16 32 95 0 257), good := (rows 359 323 78 94 351 32 66 0 256) }] }

theorem u9020 : Upper (D 7) (R 7) [36,257,10,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9021 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7),(2,7),(3,0),(3,1)], upper := (rows 37 259 14 88 145 160 96 194 322), lower := (rows 37 259 14 88 145 160 96 128 256), losses := [{ target := 7, region := (rows 1 19 28 24 16 32 97 0 283), good := (rows 359 323 270 350 351 96 96 0 256) }] }

theorem u9021 : Upper (D 7) (R 7) [36,257,10,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9021 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9022 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 322, targets := 128 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(1,7),(3,1),(4,0)], upper := (rows 37 259 14 88 146 160 65 224 352), lower := (rows 37 259 14 88 146 160 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 252 64 200 328), good := (rows 52 258 446 504 178 160 480 160 256) },{ target := 1, region := (rows 5 0 4 24 16 255 71 223 351), good := (rows 485 481 493 504 504 160 481 160 256) }] }

theorem u9022 : Upper (D 7) (R 7) [36,257,10,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9023 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 108, targets := 1 },{ cop := 0, region := 322, targets := 128 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(1,7),(2,0),(3,0)], upper := (rows 37 259 14 88 146 160 96 193 321), lower := (rows 37 259 14 88 146 160 96 128 256), losses := [] }

theorem u9023 : Upper (D 7) (R 7) [36,257,10,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9024 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 168, targets := 3 }], pairs := [(1,5),(3,0),(3,1),(4,5)], upper := (rows 37 259 14 104 81 160 66 144 400), lower := (rows 37 259 14 104 81 160 66 128 256), losses := [] }

theorem u9024 : Upper (D 7) (R 7) [36,257,10,96,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9025 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 37 259 14 104 81 160 80 130 386), lower := (rows 37 259 14 104 81 160 80 128 256), losses := [] }

theorem u9025 : Upper (D 7) (R 7) [36,257,10,96,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9025 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9026 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 259 14 104 81 160 192 146 274), lower := (rows 37 259 14 104 81 160 192 128 256), losses := [] }

theorem u9026 : Upper (D 7) (R 7) [36,257,10,96,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9026 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9027 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 72, targets := 130 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,7),(4,5)], upper := (rows 37 259 14 104 82 160 65 144 400), lower := (rows 37 259 14 104 82 160 65 128 256), losses := [] }

theorem u9027 : Upper (D 7) (R 7) [36,257,10,96,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9028 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 37 259 14 104 82 160 80 129 385), lower := (rows 37 259 14 104 82 160 80 128 256), losses := [] }

theorem u9028 : Upper (D 7) (R 7) [36,257,10,96,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9028 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9029 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 259 14 104 82 160 192 145 273), lower := (rows 37 259 14 104 82 160 192 128 256), losses := [] }

theorem u9029 : Upper (D 7) (R 7) [36,257,10,96,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9030 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 322, targets := 128 }], pairs := [(1,5),(1,7),(2,0),(4,5)], upper := (rows 37 259 14 104 145 160 66 208 336), lower := (rows 37 259 14 104 145 160 66 128 256), losses := [{ target := 0, region := (rows 0 2 6 9 16 176 70 128 256), good := (rows 108 334 78 104 184 160 70 160 256) }] }

theorem u9030 : Upper (D 7) (R 7) [36,257,10,96,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9031 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 259 14 104 145 160 80 194 322), lower := (rows 37 259 14 104 145 160 80 128 256), losses := [] }

theorem u9031 : Upper (D 7) (R 7) [36,257,10,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9031 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9032 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 72, targets := 130 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,7),(4,5)], upper := (rows 37 259 14 104 146 160 65 208 336), lower := (rows 37 259 14 104 146 160 65 128 256), losses := [] }

theorem u9032 : Upper (D 7) (R 7) [36,257,10,96,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9033 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 259 14 104 146 160 80 193 321), lower := (rows 37 259 14 104 146 160 80 128 256), losses := [] }

theorem u9033 : Upper (D 7) (R 7) [36,257,10,96,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9033 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9034 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 113, targets := 128 },{ cop := 4, region := 168, targets := 1 }], pairs := [(0,7),(3,0),(4,7)], upper := (rows 37 259 14 200 81 48 66 160 416), lower := (rows 37 259 14 200 81 48 66 128 256), losses := [] }

theorem u9034 : Upper (D 7) (R 7) [36,257,10,192,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9034 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9035 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 113, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 259 14 200 81 48 96 130 386), lower := (rows 37 259 14 200 81 48 96 128 256), losses := [] }

theorem u9035 : Upper (D 7) (R 7) [36,257,10,192,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9035 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9036 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 259 14 200 81 48 192 162 290), lower := (rows 37 259 14 200 81 48 192 128 256), losses := [] }

theorem u9036 : Upper (D 7) (R 7) [36,257,10,192,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9036 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9037 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 113, targets := 128 },{ cop := 4, region := 172, targets := 1 }], pairs := [(0,7),(2,0),(4,7)], upper := (rows 37 259 14 200 82 48 65 160 416), lower := (rows 37 259 14 200 82 48 65 128 256), losses := [] }

theorem u9037 : Upper (D 7) (R 7) [36,257,10,192,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9037 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9038 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 386, targets := 96 },{ cop := 1, region := 112, targets := 1 }], pairs := [(1,5),(1,6),(4,0)], upper := (rows 37 259 14 200 82 48 96 129 385), lower := (rows 37 259 14 200 82 48 96 128 256), losses := [] }

theorem u9038 : Upper (D 7) (R 7) [36,257,10,192,66,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9038 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9039 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 259 14 200 82 48 192 161 289), lower := (rows 37 259 14 200 82 48 192 128 256), losses := [] }

theorem u9039 : Upper (D 7) (R 7) [36,257,10,192,66,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9039 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9040 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 136, targets := 35 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(3,0),(3,1),(3,5)], upper := (rows 37 259 14 200 112 33 66 144 400), lower := (rows 37 259 14 200 112 33 66 128 256), losses := [] }

theorem u9040 : Upper (D 7) (R 7) [36,257,10,192,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9041 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 113, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 259 14 200 112 33 80 130 386), lower := (rows 37 259 14 200 112 33 80 128 256), losses := [] }

theorem u9041 : Upper (D 7) (R 7) [36,257,10,192,96,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9041 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9042 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 259 14 200 112 33 192 146 274), lower := (rows 37 259 14 200 112 33 192 128 256), losses := [] }

theorem u9042 : Upper (D 7) (R 7) [36,257,10,192,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9043 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 92, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 37 259 28 73 82 160 66 160 416), lower := (rows 37 259 28 73 82 160 66 128 256), losses := [] }

theorem u9043 : Upper (D 7) (R 7) [36,257,24,65,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9043 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9044 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 259 28 73 82 160 96 130 386), lower := (rows 37 259 28 73 82 160 96 128 256), losses := [] }

theorem u9044 : Upper (D 7) (R 7) [36,257,24,65,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9044 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9045 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 258, targets := 128 },{ cop := 1, region := 240, targets := 1 }], pairs := [(0,6),(1,6),(1,7),(4,0)], upper := (rows 37 259 28 73 82 160 192 162 290), lower := (rows 37 259 28 73 82 160 192 128 256), losses := [] }

theorem u9045 : Upper (D 7) (R 7) [36,257,24,65,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9046 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(3,0),(4,0)], upper := (rows 37 259 69 26 176 34 72 192 448), lower := (rows 37 259 69 26 176 34 72 128 256), losses := [] }

theorem u9046 : Upper (D 7) (R 7) [36,257,65,18,160,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9046 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9047 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 4, region := 69, targets := 2 }], pairs := [(0,1),(2,1),(3,0),(4,0)], upper := (rows 37 259 69 26 176 34 192 200 328), lower := (rows 37 259 69 26 176 34 192 128 256), losses := [] }

theorem u9047 : Upper (D 7) (R 7) [36,257,65,18,160,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9048 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 37 259 69 26 208 34 72 160 416), lower := (rows 37 259 69 26 208 34 72 128 256), losses := [] }

theorem u9048 : Upper (D 7) (R 7) [36,257,65,18,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9048 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9049 : PairBound 9 := { available := 136, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 69 26 208 34 96 136 392), lower := (rows 37 259 69 26 208 34 96 128 256), losses := [] }

theorem u9049 : Upper (D 7) (R 7) [36,257,65,18,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9049 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9050 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 69 26 208 34 192 168 296), lower := (rows 37 259 69 26 208 34 192 128 256), losses := [] }

theorem u9050 : Upper (D 7) (R 7) [36,257,65,18,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9051 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 1, region := 248, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 37 259 69 42 88 160 66 144 400), lower := (rows 37 259 69 42 88 160 66 128 256), losses := [] }

theorem u9051 : Upper (D 7) (R 7) [36,257,65,34,72,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9052 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 85, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 259 69 42 88 160 80 130 386), lower := (rows 37 259 69 42 88 160 80 128 256), losses := [] }

theorem u9052 : Upper (D 7) (R 7) [36,257,65,34,72,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9052 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9053 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(2,1),(3,0),(4,0)], upper := (rows 37 259 69 42 88 160 192 146 274), lower := (rows 37 259 69 42 88 160 192 128 256), losses := [] }

theorem u9053 : Upper (D 7) (R 7) [36,257,65,34,72,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9053 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9054 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 1, region := 68, targets := 160 }], pairs := [(2,5),(2,7),(3,0),(4,0)], upper := (rows 37 259 69 42 152 160 66 208 336), lower := (rows 37 259 69 42 152 160 66 128 256), losses := [] }

theorem u9054 : Upper (D 7) (R 7) [36,257,65,34,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9054 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9055 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(3,0),(4,0)], upper := (rows 37 259 69 42 152 160 80 194 322), lower := (rows 37 259 69 42 152 160 80 128 256), losses := [] }

theorem u9055 : Upper (D 7) (R 7) [36,257,65,34,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9055 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9056 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 84, targets := 160 }], pairs := [(2,5),(2,7),(4,5),(4,7)], upper := (rows 37 259 69 56 82 160 66 136 392), lower := (rows 37 259 69 56 82 160 66 128 256), losses := [] }

theorem u9056 : Upper (D 7) (R 7) [36,257,65,48,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9057 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 259 69 56 82 160 72 130 386), lower := (rows 37 259 69 56 82 160 72 128 256), losses := [] }

theorem u9057 : Upper (D 7) (R 7) [36,257,65,48,66,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9057 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9058 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(2,1),(3,0),(4,0)], upper := (rows 37 259 69 56 82 160 192 138 266), lower := (rows 37 259 69 56 82 160 192 128 256), losses := [] }

theorem u9058 : Upper (D 7) (R 7) [36,257,65,48,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9059 : PairBound 9 := { available := 136, camps := [{ cop := 8, region := 103, targets := 128 },{ cop := 1, region := 248, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 37 259 69 56 208 34 66 136 392), lower := (rows 37 259 69 56 208 34 66 128 256), losses := [] }

theorem u9059 : Upper (D 7) (R 7) [36,257,65,48,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u9059
end Delivery.IrregularNine14.P07
