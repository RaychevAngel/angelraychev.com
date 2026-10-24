import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0173
import IrregularNine14P07C0174

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28080 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 162 7 88 400 34 77 141 269), lower := (rows 97 162 7 88 400 34 64 128 256), losses := [] }

theorem u28080 : Upper (D 7) (R 7) [96,160,3,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28081 : Route 9 := (fun mask => (mask,id))

def c28081 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28081 : Upper (D 7) (R 7) [96,160,3,80,384,4] 13 := by
  apply FastRouting.sound _ _ [96,160,3,80,384,4] 13 (by decide) (choices 1) [1,2,8] r28081 c28081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10412
  · exact u10413
  · exact u10414

def b28082 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 162 7 88 400 40 71 135 263), lower := (rows 97 162 7 88 400 40 64 128 256), losses := [] }

theorem u28082 : Upper (D 7) (R 7) [96,160,3,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28082 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28083 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 162 7 200 273 34 92 156 284), lower := (rows 97 162 7 200 273 34 64 128 256), losses := [] }

theorem u28083 : Upper (D 7) (R 7) [96,160,3,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28084 : Route 9 := (fun mask => (mask,id))

def c28084 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28084 : Upper (D 7) (R 7) [96,160,3,192,257,4] 13 := by
  apply FastRouting.sound _ _ [96,160,3,192,257,4] 13 (by decide) (choices 1) [2,8,16] r28084 c28084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10415
  · exact u10416
  · exact u10417

def b28085 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 162 7 200 273 40 86 150 278), lower := (rows 97 162 7 200 273 40 64 128 256), losses := [] }

theorem u28085 : Upper (D 7) (R 7) [96,160,3,192,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28085 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28086 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 2, region := 200, targets := 1 }], pairs := [(3,0),(3,5),(4,5)], upper := (rows 97 162 7 200 273 48 78 142 270), lower := (rows 97 162 7 200 273 48 64 128 256), losses := [] }

theorem u28086 : Upper (D 7) (R 7) [96,160,3,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28086 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28087 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 162 7 200 276 33 90 154 282), lower := (rows 97 162 7 200 276 33 64 128 256), losses := [] }

theorem u28087 : Upper (D 7) (R 7) [96,160,3,192,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28088 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 162 7 200 276 40 83 147 275), lower := (rows 97 162 7 200 276 40 64 128 256), losses := [] }

theorem u28088 : Upper (D 7) (R 7) [96,160,3,192,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28088 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28089 : Route 9 := (fun mask => (mask,id))

def c28089 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28089 : Upper (D 7) (R 7) [96,160,3,192,260,16] 13 := by
  apply FastRouting.sound _ _ [96,160,3,192,260,16] 13 (by decide) (choices 1) [1,2,8] r28089 c28089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10418
  · exact u10419
  · exact u10420

def b28090 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 162 7 200 280 33 86 150 278), lower := (rows 97 162 7 200 280 33 64 128 256), losses := [] }

theorem u28090 : Upper (D 7) (R 7) [96,160,3,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28090 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28091 : Route 9 := (fun mask => (mask,id))

def c28091 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28091 : Upper (D 7) (R 7) [96,160,3,192,264,4] 13 := by
  apply FastRouting.sound _ _ [96,160,3,192,264,4] 13 (by decide) (choices 1) [1,2,16] r28091 c28091
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10421
  · exact u10422
  · exact u10423

def b28092 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 134, targets := 64 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(1,6),(2,6)], upper := (rows 97 162 7 200 280 48 71 135 263), lower := (rows 97 162 7 200 280 48 64 128 256), losses := [] }

theorem u28092 : Upper (D 7) (R 7) [96,160,3,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28092 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28093 : PairBound 9 := { available := 400, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 0, region := 402, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 97 162 13 14 82 33 464 400 400), lower := (rows 97 162 13 14 82 33 64 128 256), losses := [] }

theorem u28093 : Upper (D 7) (R 7) [96,160,9,6,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28094 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 162 13 14 82 48 449 385 385), lower := (rows 97 162 13 14 82 48 64 128 256), losses := [] }

theorem u28094 : Upper (D 7) (R 7) [96,160,9,6,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28094 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28095 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 13 14 82 160 337 401 273), lower := (rows 97 162 13 14 82 160 64 128 256), losses := [] }

theorem u28095 : Upper (D 7) (R 7) [96,160,9,6,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28096 : Route 9 := (fun mask => (mask,id))

def c28096 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28096 : Upper (D 7) (R 7) [96,160,9,6,66,256] 13 := by
  apply FastRouting.sound _ _ [96,160,9,6,66,256] 13 (by decide) (choices 1) [1,16,128] r28096 c28096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10424
  · exact u10425
  · exact u10426

def b28097 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 97 162 13 14 208 33 338 402 274), lower := (rows 97 162 13 14 208 33 64 128 256), losses := [] }

theorem u28097 : Upper (D 7) (R 7) [96,160,9,6,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28098 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 162 13 14 208 48 323 387 259), lower := (rows 97 162 13 14 208 48 64 128 256), losses := [] }

theorem u28098 : Upper (D 7) (R 7) [96,160,9,6,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28098 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28099 : Route 9 := (fun mask => (mask,id))

def c28099 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28099 : Upper (D 7) (R 7) [96,160,9,6,192,256] 13 := by
  apply FastRouting.sound _ _ [96,160,9,6,192,256] 13 (by decide) (choices 1) [1,2,16] r28099 c28099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10427
  · exact u10428
  · exact u10429

def b28100 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 400, targets := 34 },{ cop := 7, region := 34, targets := 65 }], pairs := [(1,0),(1,6),(4,1),(4,5)], upper := (rows 97 162 13 14 273 34 208 208 464), lower := (rows 97 162 13 14 273 34 64 128 256), losses := [] }

theorem u28100 : Upper (D 7) (R 7) [96,160,9,6,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28101 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 130, targets := 1 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 97 162 13 14 273 48 194 194 450), lower := (rows 97 162 13 14 273 48 64 128 256), losses := [{ target := 0, region := (rows 0 51 4 12 16 48 127 191 319), good := (rows 482 482 462 462 498 498 64 128 256) },{ target := 5, region := (rows 1 2 4 8 20 0 74 138 266), good := (rows 65 450 477 478 273 16 64 128 256) }] }

theorem u28101 : Upper (D 7) (R 7) [96,160,9,6,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28101 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28102 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 13 14 273 96 210 146 402), lower := (rows 97 162 13 14 273 96 64 128 256), losses := [] }

theorem u28102 : Upper (D 7) (R 7) [96,160,9,6,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28102 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28103 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 13 14 273 160 82 210 338), lower := (rows 97 162 13 14 273 160 64 128 256), losses := [] }

theorem u28103 : Upper (D 7) (R 7) [96,160,9,6,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28103 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28104 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 97 162 13 14 336 33 210 146 402), lower := (rows 97 162 13 14 336 33 64 128 256), losses := [] }

theorem u28104 : Upper (D 7) (R 7) [96,160,9,6,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28104 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28105 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 400, targets := 34 },{ cop := 7, region := 34, targets := 65 }], pairs := [(1,0),(1,6),(4,1),(4,5)], upper := (rows 97 162 13 14 336 34 209 145 401), lower := (rows 97 162 13 14 336 34 64 128 256), losses := [] }

theorem u28105 : Upper (D 7) (R 7) [96,160,9,6,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28106 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 142, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 162 13 14 336 48 195 131 387), lower := (rows 97 162 13 14 336 48 64 128 256), losses := [] }

theorem u28106 : Upper (D 7) (R 7) [96,160,9,6,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28106 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28107 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 13 14 336 160 83 147 275), lower := (rows 97 162 13 14 336 160 64 128 256), losses := [] }

theorem u28107 : Upper (D 7) (R 7) [96,160,9,6,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28107 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28108 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 33, targets := 130 },{ cop := 0, region := 386, targets := 1 },{ cop := 0, region := 386, targets := 64 }], pairs := [(0,1),(0,7),(1,0),(1,6)], upper := (rows 97 162 13 26 84 33 450 386 386), lower := (rows 97 162 13 26 84 33 64 128 256), losses := [] }

theorem u28108 : Upper (D 7) (R 7) [96,160,9,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28109 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 464, targets := 34 },{ cop := 7, region := 34, targets := 65 }], pairs := [(1,0),(1,6),(4,1),(4,5)], upper := (rows 97 162 13 26 84 34 449 385 385), lower := (rows 97 162 13 26 84 34 64 128 256), losses := [] }

theorem u28109 : Upper (D 7) (R 7) [96,160,9,18,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28110 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 13 26 84 160 323 387 259), lower := (rows 97 162 13 26 84 160 64 128 256), losses := [] }

theorem u28110 : Upper (D 7) (R 7) [96,160,9,18,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28111 : Route 9 := (fun mask => (mask,id))

def c28111 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28111 : Upper (D 7) (R 7) [96,160,9,18,68,256] 13 := by
  apply FastRouting.sound _ _ [96,160,9,18,68,256] 13 (by decide) (choices 1) [1,2,128] r28111 c28111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10430
  · exact u10431
  · exact u10432

def b28112 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 46, targets := 64 },{ cop := 2, region := 464, targets := 2 }], pairs := [(1,6),(2,6),(3,6),(4,1)], upper := (rows 97 162 13 26 145 34 324 452 324), lower := (rows 97 162 13 26 145 34 64 128 256), losses := [] }

theorem u28112 : Upper (D 7) (R 7) [96,160,9,18,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28112 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28113 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 46, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 162 13 26 145 36 322 450 322), lower := (rows 97 162 13 26 145 36 64 128 256), losses := [] }

theorem u28113 : Upper (D 7) (R 7) [96,160,9,18,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28113 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28114 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 13 26 145 96 326 390 262), lower := (rows 97 162 13 26 145 96 64 128 256), losses := [] }

theorem u28114 : Upper (D 7) (R 7) [96,160,9,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28114 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28115 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 357, targets := 128 },{ cop := 2, region := 482, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 97 162 13 26 145 288 70 198 326), lower := (rows 97 162 13 26 145 288 64 128 256), losses := [] }

theorem u28115 : Upper (D 7) (R 7) [96,160,9,18,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28115 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28116 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 357, targets := 128 },{ cop := 0, region := 386, targets := 1 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,0),(2,7)], upper := (rows 97 162 13 26 148 33 322 450 322), lower := (rows 97 162 13 26 148 33 64 128 256), losses := [] }

theorem u28116 : Upper (D 7) (R 7) [96,160,9,18,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28117 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 42, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 97 162 13 26 148 34 321 449 321), lower := (rows 97 162 13 26 148 34 64 128 256), losses := [] }

theorem u28117 : Upper (D 7) (R 7) [96,160,9,18,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28118 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 13 26 148 96 323 387 259), lower := (rows 97 162 13 26 148 96 64 128 256), losses := [] }

theorem u28118 : Upper (D 7) (R 7) [96,160,9,18,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28119 : Route 9 := (fun mask => (mask,id))

def c28119 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28119 : Upper (D 7) (R 7) [96,160,9,18,132,256] 13 := by
  apply FastRouting.sound _ _ [96,160,9,18,132,256] 13 (by decide) (choices 1) [1,2] r28119 c28119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10433
  · exact u10434

def b28120 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 357, targets := 128 },{ cop := 2, region := 418, targets := 64 },{ cop := 4, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,6),(2,7)], upper := (rows 97 162 13 26 208 33 326 390 262), lower := (rows 97 162 13 26 208 33 64 128 256), losses := [] }

theorem u28120 : Upper (D 7) (R 7) [96,160,9,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28121 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 42, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 97 162 13 26 208 34 325 389 261), lower := (rows 97 162 13 26 208 34 64 128 256), losses := [] }

theorem u28121 : Upper (D 7) (R 7) [96,160,9,18,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28122 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 357, targets := 128 },{ cop := 0, region := 386, targets := 64 }], pairs := [(0,7),(1,6),(2,7)], upper := (rows 97 162 13 26 208 36 323 387 259), lower := (rows 97 162 13 26 208 36 64 128 256), losses := [] }

theorem u28122 : Upper (D 7) (R 7) [96,160,9,18,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28122 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28123 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 357, targets := 128 },{ cop := 2, region := 418, targets := 64 }], pairs := [(0,7),(1,6),(2,7)], upper := (rows 97 162 13 26 208 288 71 135 263), lower := (rows 97 162 13 26 208 288 64 128 256), losses := [] }

theorem u28123 : Upper (D 7) (R 7) [96,160,9,18,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28123 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28124 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 464, targets := 34 },{ cop := 7, region := 34, targets := 65 }], pairs := [(1,0),(1,6),(4,1),(4,5)], upper := (rows 97 162 13 26 273 34 196 196 452), lower := (rows 97 162 13 26 273 34 64 128 256), losses := [] }

theorem u28124 : Upper (D 7) (R 7) [96,160,9,18,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28124 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28125 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 130, targets := 1 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 97 162 13 26 273 36 194 194 450), lower := (rows 97 162 13 26 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 39 4 24 16 36 127 191 319), good := (rows 482 482 494 474 474 486 64 128 256) },{ target := 5, region := (rows 1 2 4 8 20 0 74 138 266), good := (rows 65 450 477 474 273 20 64 128 256) }] }

theorem u28125 : Upper (D 7) (R 7) [96,160,9,18,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28125 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28126 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 13 26 273 96 198 134 390), lower := (rows 97 162 13 26 273 96 64 128 256), losses := [] }

theorem u28126 : Upper (D 7) (R 7) [96,160,9,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28127 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 13 26 273 160 70 198 326), lower := (rows 97 162 13 26 273 160 64 128 256), losses := [] }

theorem u28127 : Upper (D 7) (R 7) [96,160,9,18,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28127 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28128 : PairBound 9 := { available := 194, camps := [{ cop := 6, region := 33, targets := 130 },{ cop := 0, region := 130, targets := 1 }], pairs := [(0,1),(0,7),(1,0),(3,0)], upper := (rows 97 162 13 26 276 33 194 194 450), lower := (rows 97 162 13 26 276 33 64 128 256), losses := [{ target := 0, region := (rows 0 35 4 12 20 32 111 175 303), good := (rows 482 482 478 474 476 482 64 128 256) }] }

theorem u28128 : Upper (D 7) (R 7) [96,160,9,18,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28128 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28129 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 464, targets := 34 },{ cop := 7, region := 34, targets := 65 }], pairs := [(1,0),(1,6),(4,1),(4,5)], upper := (rows 97 162 13 26 276 34 193 193 449), lower := (rows 97 162 13 26 276 34 64 128 256), losses := [] }

theorem u28129 : Upper (D 7) (R 7) [96,160,9,18,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28129 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28130 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 13 26 276 96 195 131 387), lower := (rows 97 162 13 26 276 96 64 128 256), losses := [] }

theorem u28130 : Upper (D 7) (R 7) [96,160,9,18,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28130 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28131 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 13 26 276 160 67 195 323), lower := (rows 97 162 13 26 276 160 64 128 256), losses := [] }

theorem u28131 : Upper (D 7) (R 7) [96,160,9,18,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28132 : PairBound 9 := { available := 134, camps := [{ cop := 4, region := 33, targets := 130 },{ cop := 2, region := 162, targets := 64 }], pairs := [(0,1),(0,7),(1,6),(2,1)], upper := (rows 97 162 13 26 336 33 198 134 390), lower := (rows 97 162 13 26 336 33 64 128 256), losses := [{ target := 1, region := (rows 81 0 12 8 16 125 64 128 256), good := (rows 97 160 45 61 369 33 97 128 256) }] }

theorem u28132 : Upper (D 7) (R 7) [96,160,9,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28133 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 464, targets := 34 },{ cop := 7, region := 34, targets := 65 }], pairs := [(1,0),(1,6),(4,1),(4,5)], upper := (rows 97 162 13 26 336 34 197 133 389), lower := (rows 97 162 13 26 336 34 64 128 256), losses := [] }

theorem u28133 : Upper (D 7) (R 7) [96,160,9,18,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28133 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28134 : Route 9 := (fun mask => (mask,id))

def c28134 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28134 : Upper (D 7) (R 7) [96,160,9,18,320,4] 13 := by
  apply FastRouting.sound _ _ [96,160,9,18,320,4] 13 (by decide) (choices 1) [1,2,128] r28134 c28134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10435
  · exact u10436
  · exact u10437

def b28135 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 13 26 336 160 71 135 263), lower := (rows 97 162 13 26 336 160 64 128 256), losses := [] }

theorem u28135 : Upper (D 7) (R 7) [96,160,9,18,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28136 : Route 9 := (fun mask => (mask,id))

def c28136 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28136 : Upper (D 7) (R 7) [96,160,9,18,384,1] 13 := by
  apply FastRouting.sound _ _ [96,160,9,18,384,1] 13 (by decide) (choices 1) [2,4] r28136 c28136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10438
  · exact u10439

def b28137 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 42, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 97 162 13 26 400 34 69 197 325), lower := (rows 97 162 13 26 400 34 64 128 256), losses := [] }

theorem u28137 : Upper (D 7) (R 7) [96,160,9,18,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28138 : Route 9 := (fun mask => (mask,id))

def c28138 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28138 : Upper (D 7) (R 7) [96,160,9,18,384,4] 13 := by
  apply FastRouting.sound _ _ [96,160,9,18,384,4] 13 (by decide) (choices 1) [1,2] r28138 c28138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10440
  · exact u10441

def b28139 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 162 13 26 400 96 71 135 263), lower := (rows 97 162 13 26 400 96 64 128 256), losses := [] }

theorem u28139 : Upper (D 7) (R 7) [96,160,9,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28139 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u28139
end Delivery.IrregularNine14.P07
