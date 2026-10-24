import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0013

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10980 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 73, targets := 128 },{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1),(0,7),(3,7)], upper := (rows 97 262 38 11 145 160 72 208 336), lower := (rows 97 262 38 11 145 160 72 128 256), losses := [] }

theorem u10980 : Upper (D 7) (R 7) [96,260,34,3,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10980 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10981 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 262 38 11 145 160 80 200 328), lower := (rows 97 262 38 11 145 160 80 128 256), losses := [] }

theorem u10981 : Upper (D 7) (R 7) [96,260,34,3,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10981 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10982 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 73, targets := 128 },{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1),(0,7),(3,7),(4,1)], upper := (rows 97 262 38 11 152 160 65 208 336), lower := (rows 97 262 38 11 152 160 65 128 256), losses := [] }

theorem u10982 : Upper (D 7) (R 7) [96,260,34,3,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10982 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10983 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 262 38 11 152 160 80 193 321), lower := (rows 97 262 38 11 152 160 80 128 256), losses := [] }

theorem u10983 : Upper (D 7) (R 7) [96,260,34,3,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10983 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10984 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 73, targets := 128 },{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1),(0,7),(3,7),(4,1)], upper := (rows 97 262 38 11 208 160 65 152 280), lower := (rows 97 262 38 11 208 160 65 128 256), losses := [] }

theorem u10984 : Upper (D 7) (R 7) [96,260,34,3,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10984 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10985 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 73, targets := 128 },{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1),(0,7),(3,7)], upper := (rows 97 262 38 11 208 160 72 145 273), lower := (rows 97 262 38 11 208 160 72 128 256), losses := [] }

theorem u10985 : Upper (D 7) (R 7) [96,260,34,3,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10985 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10986 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 270, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 38 11 208 160 80 137 265), lower := (rows 97 262 38 11 208 160 80 128 256), losses := [] }

theorem u10986 : Upper (D 7) (R 7) [96,260,34,3,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10986 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10987 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 89, targets := 128 },{ cop := 0, region := 390, targets := 1 }], pairs := [(0,7),(1,0),(3,7),(4,7)], upper := (rows 97 262 38 25 26 160 65 192 448), lower := (rows 97 262 38 25 26 160 65 128 256), losses := [] }

theorem u10987 : Upper (D 7) (R 7) [96,260,34,17,10,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10988 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 262 38 25 26 160 192 193 321), lower := (rows 97 262 38 25 26 160 192 128 256), losses := [] }

theorem u10988 : Upper (D 7) (R 7) [96,260,34,17,10,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10988 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10989 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 97 262 38 25 146 33 72 192 448), lower := (rows 97 262 38 25 146 33 72 128 256), losses := [] }

theorem u10989 : Upper (D 7) (R 7) [96,260,34,17,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10989 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r10990 : Route 9 := (fun mask => (mask,id))

def c10990 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u10990 : Upper (D 7) (R 7) [96,260,34,17,130,1,128] 13 := by
  apply FastRouting.sound _ _ [96,260,34,17,130,1,128] 13 (by decide) (choices 1) [8,64] r10990 c10990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u817
  · exact u818

def b10991 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 97 262 38 25 146 40 65 192 448), lower := (rows 97 262 38 25 146 40 65 128 256), losses := [] }

theorem u10991 : Upper (D 7) (R 7) [96,260,34,17,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10991 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10992 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 262, targets := 128 },{ cop := 4, region := 105, targets := 2 }], pairs := [(0,1),(1,7),(2,7)], upper := (rows 97 262 38 25 146 40 192 193 321), lower := (rows 97 262 38 25 146 40 192 128 256), losses := [] }

theorem u10992 : Upper (D 7) (R 7) [96,260,34,17,130,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10992 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10993 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 89, targets := 2 },{ cop := 5, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,1)], upper := (rows 97 262 38 25 152 160 65 194 322), lower := (rows 97 262 38 25 152 160 65 128 256), losses := [] }

theorem u10993 : Upper (D 7) (R 7) [96,260,34,17,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10994 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 6, region := 161, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 97 262 38 25 152 160 66 193 321), lower := (rows 97 262 38 25 152 160 66 128 256), losses := [] }

theorem u10994 : Upper (D 7) (R 7) [96,260,34,17,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10994 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10995 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 262 38 74 145 48 65 136 392), lower := (rows 97 262 38 74 145 48 65 128 256), losses := [] }

theorem u10995 : Upper (D 7) (R 7) [96,260,34,66,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10995 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10996 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 262 38 74 145 48 72 129 385), lower := (rows 97 262 38 74 145 48 72 128 256), losses := [] }

theorem u10996 : Upper (D 7) (R 7) [96,260,34,66,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10996 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10997 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 262 38 74 145 48 192 137 265), lower := (rows 97 262 38 74 145 48 192 128 256), losses := [] }

theorem u10997 : Upper (D 7) (R 7) [96,260,34,66,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10997 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10998 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 73, targets := 128 },{ cop := 3, region := 177, targets := 2 }], pairs := [(0,1),(0,7),(3,7),(4,1)], upper := (rows 97 262 38 74 145 160 65 152 280), lower := (rows 97 262 38 74 145 160 65 128 256), losses := [] }

theorem u10998 : Upper (D 7) (R 7) [96,260,34,66,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10999 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 262 38 74 145 160 72 145 273), lower := (rows 97 262 38 74 145 160 72 128 256), losses := [] }

theorem u10999 : Upper (D 7) (R 7) [96,260,34,66,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10999 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11000 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 262 38 74 145 160 80 137 265), lower := (rows 97 262 38 74 145 160 80 128 256), losses := [] }

theorem u11000 : Upper (D 7) (R 7) [96,260,34,66,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11000 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11001 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 73, targets := 128 },{ cop := 3, region := 177, targets := 2 }], pairs := [(0,1),(0,7),(3,7),(4,1)], upper := (rows 97 262 38 74 152 160 65 145 273), lower := (rows 97 262 38 74 152 160 65 128 256), losses := [] }

theorem u11001 : Upper (D 7) (R 7) [96,260,34,66,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11002 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 262 38 74 152 160 80 129 257), lower := (rows 97 262 38 74 152 160 80 128 256), losses := [] }

theorem u11002 : Upper (D 7) (R 7) [96,260,34,66,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11002 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11003 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 262 38 88 145 160 65 138 266), lower := (rows 97 262 38 88 145 160 65 128 256), losses := [] }

theorem u11003 : Upper (D 7) (R 7) [96,260,34,80,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11004 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 185, targets := 2 },{ cop := 0, region := 152, targets := 32 }], pairs := [(0,1),(3,1),(3,5),(4,1)], upper := (rows 97 262 38 88 145 160 66 137 265), lower := (rows 97 262 38 88 145 160 66 128 256), losses := [] }

theorem u11004 : Upper (D 7) (R 7) [96,260,34,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11004 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11005 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 262 38 88 145 160 72 131 259), lower := (rows 97 262 38 88 145 160 72 128 256), losses := [] }

theorem u11005 : Upper (D 7) (R 7) [96,260,34,80,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11005 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11006 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 262 38 88 146 33 65 136 392), lower := (rows 97 262 38 88 146 33 65 128 256), losses := [] }

theorem u11006 : Upper (D 7) (R 7) [96,260,34,80,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11006 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11007 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 262 38 88 146 33 72 129 385), lower := (rows 97 262 38 88 146 33 72 128 256), losses := [] }

theorem u11007 : Upper (D 7) (R 7) [96,260,34,80,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11007 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11008 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 97 262 38 88 146 33 192 137 265), lower := (rows 97 262 38 88 146 33 192 128 256), losses := [] }

theorem u11008 : Upper (D 7) (R 7) [96,260,34,80,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11008 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11009 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 97 262 38 137 146 33 72 208 336), lower := (rows 97 262 38 137 146 33 72 128 256), losses := [] }

theorem u11009 : Upper (D 7) (R 7) [96,260,34,129,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11009 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11010 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 105, targets := 2 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 97 262 38 137 146 33 80 200 328), lower := (rows 97 262 38 137 146 33 80 128 256), losses := [] }

theorem u11010 : Upper (D 7) (R 7) [96,260,34,129,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11010 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11011 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 97 262 38 137 146 40 65 208 336), lower := (rows 97 262 38 137 146 40 65 128 256), losses := [] }

theorem u11011 : Upper (D 7) (R 7) [96,260,34,129,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11011 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11012 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 262, targets := 128 }], pairs := [(1,7),(2,7)], upper := (rows 97 262 38 137 146 40 80 193 321), lower := (rows 97 262 38 137 146 40 80 128 256), losses := [] }

theorem u11012 : Upper (D 7) (R 7) [96,260,34,129,130,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11012 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11013 : PairBound 9 := { available := 24, camps := [{ cop := 6, region := 185, targets := 2 },{ cop := 8, region := 103, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,1)], upper := (rows 97 262 38 137 208 33 66 152 280), lower := (rows 97 262 38 137 208 33 66 128 256), losses := [] }

theorem u11013 : Upper (D 7) (R 7) [96,260,34,129,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11013 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11014 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 97 262 38 137 208 33 72 146 274), lower := (rows 97 262 38 137 208 33 72 128 256), losses := [] }

theorem u11014 : Upper (D 7) (R 7) [96,260,34,129,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11014 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11015 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 38 137 208 33 80 138 266), lower := (rows 97 262 38 137 208 33 80 128 256), losses := [] }

theorem u11015 : Upper (D 7) (R 7) [96,260,34,129,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11015 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11016 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 97 262 38 137 208 40 65 146 274), lower := (rows 97 262 38 137 208 40 65 128 256), losses := [] }

theorem u11016 : Upper (D 7) (R 7) [96,260,34,129,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11016 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11017 : PairBound 9 := { available := 17, camps := [{ cop := 6, region := 185, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 97 262 38 137 208 40 66 145 273), lower := (rows 97 262 38 137 208 40 66 128 256), losses := [] }

theorem u11017 : Upper (D 7) (R 7) [96,260,34,129,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11017 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11018 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 262, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 262 38 137 208 40 80 131 259), lower := (rows 97 262 38 137 208 40 80 128 256), losses := [] }

theorem u11018 : Upper (D 7) (R 7) [96,260,34,129,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11018 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11019 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 262 38 138 208 33 65 152 280), lower := (rows 97 262 38 138 208 33 65 128 256), losses := [] }

theorem u11019 : Upper (D 7) (R 7) [96,260,34,130,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11020 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 262 38 138 208 33 72 145 273), lower := (rows 97 262 38 138 208 33 72 128 256), losses := [] }

theorem u11020 : Upper (D 7) (R 7) [96,260,34,130,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11020 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11021 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 38 138 208 33 80 137 265), lower := (rows 97 262 38 138 208 33 80 128 256), losses := [] }

theorem u11021 : Upper (D 7) (R 7) [96,260,34,130,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11021 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11022 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 65, targets := 130 },{ cop := 3, region := 80, targets := 32 },{ cop := 3, region := 80, targets := 128 }], pairs := [(0,1),(0,7),(4,5),(4,7)], upper := (rows 97 262 44 11 82 160 65 144 400), lower := (rows 97 262 44 11 82 160 65 128 256), losses := [] }

theorem u11022 : Upper (D 7) (R 7) [96,260,40,3,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11023 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 44 11 82 160 80 129 385), lower := (rows 97 262 44 11 82 160 80 128 256), losses := [] }

theorem u11023 : Upper (D 7) (R 7) [96,260,40,3,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11023 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11024 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 262 44 11 82 160 192 145 273), lower := (rows 97 262 44 11 82 160 192 128 256), losses := [] }

theorem u11024 : Upper (D 7) (R 7) [96,260,40,3,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11025 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 177, targets := 2 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,1),(2,1),(4,1),(4,5)], upper := (rows 97 262 44 11 145 160 66 208 336), lower := (rows 97 262 44 11 145 160 66 128 256), losses := [{ target := 1, region := (rows 65 0 12 8 89 249 64 193 321), good := (rows 497 260 60 445 433 160 497 160 256) }] }

theorem u11025 : Upper (D 7) (R 7) [96,260,40,3,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11026 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 262 44 11 145 160 80 194 322), lower := (rows 97 262 44 11 145 160 80 128 256), losses := [] }

theorem u11026 : Upper (D 7) (R 7) [96,260,40,3,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11026 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11027 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 65, targets := 130 },{ cop := 3, region := 208, targets := 32 }], pairs := [(0,1),(0,7),(1,5),(4,5)], upper := (rows 97 262 44 11 146 160 65 208 336), lower := (rows 97 262 44 11 146 160 65 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 30 0 73 140 268), good := (rows 65 406 478 475 146 128 65 128 256) }] }

theorem u11027 : Upper (D 7) (R 7) [96,260,40,3,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11028 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 262 44 11 146 160 80 193 321), lower := (rows 97 262 44 11 146 160 80 128 256), losses := [] }

theorem u11028 : Upper (D 7) (R 7) [96,260,40,3,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11028 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11029 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 65, targets := 130 },{ cop := 3, region := 208, targets := 32 },{ cop := 5, region := 81, targets := 2 }], pairs := [(0,1),(0,7),(4,1),(4,5)], upper := (rows 97 262 44 11 208 160 65 146 274), lower := (rows 97 262 44 11 208 160 65 128 256), losses := [] }

theorem u11029 : Upper (D 7) (R 7) [96,260,40,3,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11030 : PairBound 9 := { available := 17, camps := [{ cop := 6, region := 177, targets := 2 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,1),(2,1),(4,1),(4,5)], upper := (rows 97 262 44 11 208 160 66 145 273), lower := (rows 97 262 44 11 208 160 66 128 256), losses := [{ target := 1, region := (rows 81 0 12 8 81 253 64 217 345), good := (rows 497 292 428 445 497 160 497 160 256) }] }

theorem u11030 : Upper (D 7) (R 7) [96,260,40,3,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11031 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 270, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 44 11 208 160 80 131 259), lower := (rows 97 262 44 11 208 160 80 128 256), losses := [] }

theorem u11031 : Upper (D 7) (R 7) [96,260,40,3,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11031 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11032 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 262 44 25 82 160 65 130 386), lower := (rows 97 262 44 25 82 160 65 128 256), losses := [] }

theorem u11032 : Upper (D 7) (R 7) [96,260,40,17,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11033 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 80, targets := 161 },{ cop := 4, region := 161, targets := 2 }], pairs := [(0,1),(4,0),(4,5),(4,7)], upper := (rows 97 262 44 25 82 160 66 129 385), lower := (rows 97 262 44 25 82 160 66 128 256), losses := [] }

theorem u11033 : Upper (D 7) (R 7) [96,260,40,17,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11033 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11034 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 262 44 25 82 160 192 131 259), lower := (rows 97 262 44 25 82 160 192 128 256), losses := [] }

theorem u11034 : Upper (D 7) (R 7) [96,260,40,17,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11035 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 262 44 25 208 34 65 130 386), lower := (rows 97 262 44 25 208 34 65 128 256), losses := [] }

theorem u11035 : Upper (D 7) (R 7) [96,260,40,17,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11035 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11036 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 0, region := 152, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 97 262 44 25 208 34 66 129 385), lower := (rows 97 262 44 25 208 34 66 128 256), losses := [] }

theorem u11036 : Upper (D 7) (R 7) [96,260,40,17,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11037 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 97 262 44 25 208 34 192 131 259), lower := (rows 97 262 44 25 208 34 192 128 256), losses := [] }

theorem u11037 : Upper (D 7) (R 7) [96,260,40,17,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11037 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11038 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 65, targets := 130 },{ cop := 4, region := 72, targets := 32 },{ cop := 4, region := 72, targets := 128 }], pairs := [(0,1),(0,7),(3,5),(3,7)], upper := (rows 97 262 44 74 19 160 65 144 400), lower := (rows 97 262 44 74 19 160 65 128 256), losses := [] }

theorem u11038 : Upper (D 7) (R 7) [96,260,40,66,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11039 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 165, targets := 2 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,1),(2,1),(3,0)], upper := (rows 97 262 44 74 19 160 80 129 385), lower := (rows 97 262 44 74 19 160 80 128 256), losses := [] }

theorem u11039 : Upper (D 7) (R 7) [96,260,40,66,3,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11039 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u11039
end Delivery.IrregularNine14.P07
