import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0079

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18000 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 496, targets := 1 }], pairs := [(2,6),(3,6),(4,0),(4,6)], upper := (rows 35 67 13 138 176 96 340 404 276), lower := (rows 35 67 13 138 176 96 64 128 256), losses := [] }

theorem u18000 : Upper (D 7) (R 7) [34,65,9,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18001 : Route 9 := (fun mask => (mask,id))

def c18001 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18001 : Upper (D 7) (R 7) [34,65,9,130,160,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,130,160,256] 13 (by decide) (choices 1) [4,16] r18001 c18001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4758
  · exact u4759

def b18002 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 67 13 138 208 36 368 432 304), lower := (rows 35 67 13 138 208 36 64 128 256), losses := [] }

theorem u18002 : Upper (D 7) (R 7) [34,65,9,130,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18002 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18003 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 2, region := 496, targets := 1 }], pairs := [(2,6),(3,6),(4,0)], upper := (rows 35 67 13 138 208 48 356 420 292), lower := (rows 35 67 13 138 208 48 64 128 256), losses := [] }

theorem u18003 : Upper (D 7) (R 7) [34,65,9,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18003 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18004 : Route 9 := (fun mask => (mask,id))

def c18004 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18004 : Upper (D 7) (R 7) [34,65,9,130,192,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,130,192,256] 13 (by decide) (choices 1) [4,16,32] r18004 c18004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4760
  · exact u4761
  · exact u4762

def b18005 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 496, targets := 3 },{ cop := 0, region := 200, targets := 1 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 35 67 13 138 276 48 224 224 480), lower := (rows 35 67 13 138 276 48 64 128 256), losses := [] }

theorem u18005 : Upper (D 7) (R 7) [34,65,9,130,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18005 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18006 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 496, targets := 1 }], pairs := [(2,6),(3,6),(4,0),(4,6)], upper := (rows 35 67 13 138 276 96 240 176 432), lower := (rows 35 67 13 138 276 96 64 128 256), losses := [] }

theorem u18006 : Upper (D 7) (R 7) [34,65,9,130,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18006 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18007 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 496, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,6),(4,0),(4,1)], upper := (rows 35 67 13 138 276 160 112 240 368), lower := (rows 35 67 13 138 276 160 64 128 256), losses := [] }

theorem u18007 : Upper (D 7) (R 7) [34,65,9,130,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18008 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 67 13 138 304 36 208 208 464), lower := (rows 35 67 13 138 304 36 64 128 256), losses := [] }

theorem u18008 : Upper (D 7) (R 7) [34,65,9,130,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18008 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18009 : PairBound 9 := { available := 196, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 67 13 138 304 48 196 196 452), lower := (rows 35 67 13 138 304 48 64 128 256), losses := [] }

theorem u18009 : Upper (D 7) (R 7) [34,65,9,130,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18009 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18010 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 496, targets := 1 }], pairs := [(2,6),(3,6),(4,0),(4,6)], upper := (rows 35 67 13 138 304 96 212 148 404), lower := (rows 35 67 13 138 304 96 64 128 256), losses := [] }

theorem u18010 : Upper (D 7) (R 7) [34,65,9,130,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18011 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 496, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,6),(4,0),(4,1)], upper := (rows 35 67 13 138 304 160 84 212 340), lower := (rows 35 67 13 138 304 160 64 128 256), losses := [] }

theorem u18011 : Upper (D 7) (R 7) [34,65,9,130,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18012 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 67 13 138 336 36 240 176 432), lower := (rows 35 67 13 138 336 36 64 128 256), losses := [] }

theorem u18012 : Upper (D 7) (R 7) [34,65,9,130,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18012 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18013 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 2, region := 496, targets := 1 }], pairs := [(2,6),(3,6),(4,0)], upper := (rows 35 67 13 138 336 48 228 164 420), lower := (rows 35 67 13 138 336 48 64 128 256), losses := [] }

theorem u18013 : Upper (D 7) (R 7) [34,65,9,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18013 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18014 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 496, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,6),(4,0),(4,1)], upper := (rows 35 67 13 138 336 160 116 180 308), lower := (rows 35 67 13 138 336 160 64 128 256), losses := [] }

theorem u18014 : Upper (D 7) (R 7) [34,65,9,130,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18014 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18015 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 67 13 138 400 36 112 240 368), lower := (rows 35 67 13 138 400 36 64 128 256), losses := [] }

theorem u18015 : Upper (D 7) (R 7) [34,65,9,130,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18015 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18016 : Route 9 := (fun mask => (mask,id))

def c18016 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18016 : Upper (D 7) (R 7) [34,65,9,130,384,16] 13 := by
  apply FastRouting.sound _ _ [34,65,9,130,384,16] 13 (by decide) (choices 1) [4,32] r18016 c18016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4763
  · exact u4764

def b18017 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 496, targets := 1 }], pairs := [(2,6),(3,6),(4,0),(4,6)], upper := (rows 35 67 13 138 400 96 116 180 308), lower := (rows 35 67 13 138 400 96 64 128 256), losses := [] }

theorem u18017 : Upper (D 7) (R 7) [34,65,9,130,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18018 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 67 13 140 274 48 224 224 480), lower := (rows 35 67 13 140 274 48 64 128 256), losses := [] }

theorem u18018 : Upper (D 7) (R 7) [34,65,9,132,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18018 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18019 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 140 274 96 240 176 432), lower := (rows 35 67 13 140 274 96 64 128 256), losses := [] }

theorem u18019 : Upper (D 7) (R 7) [34,65,9,132,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18020 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 339, targets := 128 },{ cop := 0, region := 336, targets := 1 }], pairs := [(0,7),(1,7),(4,0),(4,7)], upper := (rows 35 67 13 140 274 160 112 240 368), lower := (rows 35 67 13 140 274 160 64 128 256), losses := [] }

theorem u18020 : Upper (D 7) (R 7) [34,65,9,132,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18021 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 140 304 34 208 208 464), lower := (rows 35 67 13 140 304 34 64 128 256), losses := [] }

theorem u18021 : Upper (D 7) (R 7) [34,65,9,132,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18021 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18022 : PairBound 9 := { available := 194, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 67 13 140 304 48 194 194 450), lower := (rows 35 67 13 140 304 48 64 128 256), losses := [] }

theorem u18022 : Upper (D 7) (R 7) [34,65,9,132,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18022 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18023 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 140 304 96 210 146 402), lower := (rows 35 67 13 140 304 96 64 128 256), losses := [] }

theorem u18023 : Upper (D 7) (R 7) [34,65,9,132,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18024 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 339, targets := 128 },{ cop := 0, region := 336, targets := 1 }], pairs := [(0,7),(1,7),(4,0),(4,7)], upper := (rows 35 67 13 140 304 160 82 210 338), lower := (rows 35 67 13 140 304 160 64 128 256), losses := [] }

theorem u18024 : Upper (D 7) (R 7) [34,65,9,132,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18025 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 140 336 34 240 176 432), lower := (rows 35 67 13 140 336 34 64 128 256), losses := [] }

theorem u18025 : Upper (D 7) (R 7) [34,65,9,132,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18026 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 67 13 140 336 48 226 162 418), lower := (rows 35 67 13 140 336 48 64 128 256), losses := [] }

theorem u18026 : Upper (D 7) (R 7) [34,65,9,132,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18026 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18027 : PairBound 9 := { available := 50, camps := [{ cop := 5, region := 339, targets := 128 },{ cop := 0, region := 336, targets := 1 }], pairs := [(0,7),(1,7),(4,0),(4,7)], upper := (rows 35 67 13 140 336 160 114 178 306), lower := (rows 35 67 13 140 336 160 64 128 256), losses := [] }

theorem u18027 : Upper (D 7) (R 7) [34,65,9,132,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18028 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 152 84 34 480 416 416), lower := (rows 35 67 13 152 84 34 64 128 256), losses := [] }

theorem u18028 : Upper (D 7) (R 7) [34,65,9,144,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18029 : PairBound 9 := { available := 290, camps := [{ cop := 5, region := 323, targets := 128 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(3,0)], upper := (rows 35 67 13 152 84 160 354 418 290), lower := (rows 35 67 13 152 84 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 175 67 131 259), good := (rows 482 482 508 184 124 160 64 160 256) }] }

theorem u18029 : Upper (D 7) (R 7) [34,65,9,144,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18030 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 35 67 13 152 84 288 226 162 418), lower := (rows 35 67 13 152 84 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 295 67 131 259), good := (rows 482 482 508 152 124 288 64 128 288) }] }

theorem u18030 : Upper (D 7) (R 7) [34,65,9,144,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18030 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18031 : Route 9 := (fun mask => (mask,id))

def c18031 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u18031 : Upper (D 7) (R 7) [34,65,9,144,258,4] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,258,4] 13 (by decide) (choices 1) [32,128] r18031 c18031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4765
  · exact u4766

def b18032 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 152 274 96 228 164 420), lower := (rows 35 67 13 152 274 96 64 128 256), losses := [] }

theorem u18032 : Upper (D 7) (R 7) [34,65,9,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18033 : Route 9 := (fun mask => (mask,id))

def c18033 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18033 : Upper (D 7) (R 7) [34,65,9,144,258,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,258,128] 13 (by decide) (choices 1) [4,32] r18033 c18033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4767
  · exact u4768

def b18034 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 152 276 34 224 224 480), lower := (rows 35 67 13 152 276 34 64 128 256), losses := [] }

theorem u18034 : Upper (D 7) (R 7) [34,65,9,144,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18035 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 152 276 96 226 162 418), lower := (rows 35 67 13 152 276 96 64 128 256), losses := [] }

theorem u18035 : Upper (D 7) (R 7) [34,65,9,144,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18035 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18036 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 152 276 160 98 226 354), lower := (rows 35 67 13 152 276 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 175 67 131 259), good := (rows 482 482 508 184 316 160 64 160 256) }] }

theorem u18036 : Upper (D 7) (R 7) [34,65,9,144,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18037 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 152 304 34 196 196 452), lower := (rows 35 67 13 152 304 34 64 128 256), losses := [] }

theorem u18037 : Upper (D 7) (R 7) [34,65,9,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18037 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18038 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 13 152 304 36 194 194 450), lower := (rows 35 67 13 152 304 36 64 128 256), losses := [] }

theorem u18038 : Upper (D 7) (R 7) [34,65,9,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18038 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18039 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 152 304 96 198 134 390), lower := (rows 35 67 13 152 304 96 64 128 256), losses := [] }

theorem u18039 : Upper (D 7) (R 7) [34,65,9,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18039 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18040 : Route 9 := (fun mask => (mask,id))

def c18040 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18040 : Upper (D 7) (R 7) [34,65,9,144,288,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,288,128] 13 (by decide) (choices 1) [2,4] r18040 c18040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4769
  · exact u4770

def b18041 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 152 336 34 228 164 420), lower := (rows 35 67 13 152 336 34 64 128 256), losses := [] }

theorem u18041 : Upper (D 7) (R 7) [34,65,9,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18041 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18042 : Route 9 := (fun mask => (mask,id))

def c18042 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u18042 : Upper (D 7) (R 7) [34,65,9,144,320,4] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,320,4] 13 (by decide) (choices 1) [2,32,128] r18042 c18042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4771
  · exact u4772
  · exact u4773

def r18043 : Route 9 := (fun mask => (mask,id))

def c18043 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18043 : Upper (D 7) (R 7) [34,65,9,144,320,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,320,128] 13 (by decide) (choices 1) [2,4,32] r18043 c18043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4774
  · exact u4775
  · exact u4776

def b18044 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 168 84 34 464 400 400), lower := (rows 35 67 13 168 84 34 64 128 256), losses := [] }

theorem u18044 : Upper (D 7) (R 7) [34,65,9,160,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18044 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18045 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(2,6),(3,6)], upper := (rows 35 67 13 168 84 48 450 386 386), lower := (rows 35 67 13 168 84 48 64 128 256), losses := [] }

theorem u18045 : Upper (D 7) (R 7) [34,65,9,160,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18045 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18046 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 67 13 168 84 160 338 402 274), lower := (rows 35 67 13 168 84 160 64 128 256), losses := [] }

theorem u18046 : Upper (D 7) (R 7) [34,65,9,160,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18046 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18047 : Route 9 := (fun mask => (mask,id))

def c18047 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18047 : Upper (D 7) (R 7) [34,65,9,160,68,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,160,68,256] 13 (by decide) (choices 1) [2,16,128] r18047 c18047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4777
  · exact u4778
  · exact u4779

def b18048 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 67 13 168 146 36 336 464 336), lower := (rows 35 67 13 168 146 36 64 128 256), losses := [] }

theorem u18048 : Upper (D 7) (R 7) [34,65,9,160,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18048 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18049 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 168 146 48 324 452 324), lower := (rows 35 67 13 168 146 48 64 128 256), losses := [] }

theorem u18049 : Upper (D 7) (R 7) [34,65,9,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18049 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18050 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 168 146 96 340 404 276), lower := (rows 35 67 13 168 146 96 64 128 256), losses := [] }

theorem u18050 : Upper (D 7) (R 7) [34,65,9,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18051 : Route 9 := (fun mask => (mask,id))

def c18051 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18051 : Upper (D 7) (R 7) [34,65,9,160,130,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,160,130,256] 13 (by decide) (choices 1) [4,16] r18051 c18051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4780
  · exact u4781

def b18052 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 168 208 34 340 404 276), lower := (rows 35 67 13 168 208 34 64 128 256), losses := [] }

theorem u18052 : Upper (D 7) (R 7) [34,65,9,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18052 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18053 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 13 168 208 36 338 402 274), lower := (rows 35 67 13 168 208 36 64 128 256), losses := [] }

theorem u18053 : Upper (D 7) (R 7) [34,65,9,160,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18053 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18054 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 168 208 48 326 390 262), lower := (rows 35 67 13 168 208 48 64 128 256), losses := [] }

theorem u18054 : Upper (D 7) (R 7) [34,65,9,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18054 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18055 : Route 9 := (fun mask => (mask,id))

def c18055 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18055 : Upper (D 7) (R 7) [34,65,9,160,192,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,160,192,256] 13 (by decide) (choices 1) [2,4,16] r18055 c18055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4782
  · exact u4783
  · exact u4784

def b18056 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 13 168 274 36 208 208 464), lower := (rows 35 67 13 168 274 36 64 128 256), losses := [] }

theorem u18056 : Upper (D 7) (R 7) [34,65,9,160,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18056 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18057 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 35 67 13 168 274 48 196 196 452), lower := (rows 35 67 13 168 274 48 64 128 256), losses := [] }

theorem u18057 : Upper (D 7) (R 7) [34,65,9,160,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18057 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18058 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 168 274 96 212 148 404), lower := (rows 35 67 13 168 274 96 64 128 256), losses := [] }

theorem u18058 : Upper (D 7) (R 7) [34,65,9,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18059 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 67 13 168 274 160 84 212 340), lower := (rows 35 67 13 168 274 160 64 128 256), losses := [] }

theorem u18059 : Upper (D 7) (R 7) [34,65,9,160,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u18059
end Delivery.IrregularNine14.P07
