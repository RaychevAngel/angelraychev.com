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

def b7980 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 290, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 98 140 73 146 288 80 131 259), lower := (rows 37 98 140 73 146 288 80 128 256), losses := [{ target := 7, region := (rows 5 10 4 8 16 301 80 0 268), good := (rows 293 98 303 363 82 288 80 0 288) }] }

theorem u7980 : Upper (D 7) (R 7) [36,96,136,65,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7980 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7981 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 404, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(4,1)], upper := (rows 37 98 140 73 273 34 66 144 400), lower := (rows 37 98 140 73 273 34 66 128 256), losses := [] }

theorem u7981 : Upper (D 7) (R 7) [36,96,136,65,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7981 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7982 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 166, targets := 1 },{ cop := 4, region := 72, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 37 98 140 73 273 34 80 130 386), lower := (rows 37 98 140 73 273 34 80 128 256), losses := [] }

theorem u7982 : Upper (D 7) (R 7) [36,96,136,65,257,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7982 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7983 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 306, targets := 128 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(1,7),(3,1),(4,7)], upper := (rows 37 98 140 73 273 34 192 146 274), lower := (rows 37 98 140 73 273 34 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 32 196 128 256), good := (rows 109 96 204 73 281 32 192 192 256) }] }

theorem u7983 : Upper (D 7) (R 7) [36,96,136,65,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7984 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 0, region := 66, targets := 1 }], pairs := [(1,0),(1,7),(3,7)], upper := (rows 37 98 140 73 273 48 66 130 386), lower := (rows 37 98 140 73 273 48 66 128 256), losses := [] }

theorem u7984 : Upper (D 7) (R 7) [36,96,136,65,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7984 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7985 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 306, targets := 128 },{ cop := 0, region := 194, targets := 1 }], pairs := [(1,0),(1,7),(4,7)], upper := (rows 37 98 140 73 273 48 192 130 258), lower := (rows 37 98 140 73 273 48 192 128 256), losses := [] }

theorem u7985 : Upper (D 7) (R 7) [36,96,136,65,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7985 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7986 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 107, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 37 98 140 73 274 34 65 144 400), lower := (rows 37 98 140 73 274 34 65 128 256), losses := [] }

theorem u7986 : Upper (D 7) (R 7) [36,96,136,65,258,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7987 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 140 73 274 34 80 129 385), lower := (rows 37 98 140 73 274 34 80 128 256), losses := [] }

theorem u7987 : Upper (D 7) (R 7) [36,96,136,65,258,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7987 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7988 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 306, targets := 128 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(1,7),(3,1),(4,7)], upper := (rows 37 98 140 73 274 34 192 145 273), lower := (rows 37 98 140 73 274 34 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 32 196 128 256), good := (rows 109 96 204 73 272 32 192 192 256) }] }

theorem u7988 : Upper (D 7) (R 7) [36,96,136,65,258,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7988 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7989 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 37 98 140 73 274 48 65 130 386), lower := (rows 37 98 140 73 274 48 65 128 256), losses := [] }

theorem u7989 : Upper (D 7) (R 7) [36,96,136,65,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7989 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7990 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 140 73 274 48 66 129 385), lower := (rows 37 98 140 73 274 48 66 128 256), losses := [] }

theorem u7990 : Upper (D 7) (R 7) [36,96,136,65,258,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7990 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7991 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 306, targets := 128 }], pairs := [(1,0),(1,7),(4,7)], upper := (rows 37 98 140 73 274 48 192 131 259), lower := (rows 37 98 140 73 274 48 192 128 256), losses := [{ target := 0, region := (rows 0 3 4 8 16 48 196 128 256), good := (rows 102 98 204 74 306 48 192 192 256) }] }

theorem u7991 : Upper (D 7) (R 7) [36,96,136,65,258,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7991 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7992 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 107, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 37 98 140 73 400 34 65 146 274), lower := (rows 37 98 140 73 400 34 65 128 256), losses := [] }

theorem u7992 : Upper (D 7) (R 7) [36,96,136,65,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7993 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 404, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(4,1)], upper := (rows 37 98 140 73 400 34 66 145 273), lower := (rows 37 98 140 73 400 34 66 128 256), losses := [] }

theorem u7993 : Upper (D 7) (R 7) [36,96,136,65,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7994 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 98, targets := 129 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 140 73 400 34 80 131 259), lower := (rows 37 98 140 73 400 34 80 128 256), losses := [{ target := 7, region := (rows 5 90 4 8 16 126 80 0 268), good := (rows 293 98 303 363 370 34 114 0 256) }] }

theorem u7994 : Upper (D 7) (R 7) [36,96,136,65,384,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7994 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7995 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 37 98 140 73 400 48 65 130 258), lower := (rows 37 98 140 73 400 48 65 128 256), losses := [] }

theorem u7995 : Upper (D 7) (R 7) [36,96,136,65,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7995 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7996 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 0, region := 66, targets := 1 }], pairs := [(1,0),(1,7),(3,7)], upper := (rows 37 98 140 73 400 48 66 131 259), lower := (rows 37 98 140 73 400 48 66 128 256), losses := [] }

theorem u7996 : Upper (D 7) (R 7) [36,96,136,65,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7996 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7997 : Route 9 := (fun mask => (mask,id))

def c7997 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7997 : Upper (D 7) (R 7) [36,96,136,80,130,256,1] 13 := by
  apply FastRouting.sound _ _ [36,96,136,80,130,256,1] 13 (by decide) (choices 1) [1,2] r7997 c7997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u620
  · exact u621

def b7998 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 421, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 140 88 146 288 66 129 257), lower := (rows 37 98 140 88 146 288 66 128 256), losses := [] }

theorem u7998 : Upper (D 7) (R 7) [36,96,136,80,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7998 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7999 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 3, region := 166, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 37 98 140 88 273 34 65 130 386), lower := (rows 37 98 140 88 273 34 65 128 256), losses := [] }

theorem u7999 : Upper (D 7) (R 7) [36,96,136,80,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8000 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 140 88 273 34 66 129 385), lower := (rows 37 98 140 88 273 34 66 128 256), losses := [] }

theorem u8000 : Upper (D 7) (R 7) [36,96,136,80,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8001 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 34, targets := 129 }], pairs := [(0,7),(1,0),(1,7),(4,7)], upper := (rows 37 98 140 88 273 34 192 131 259), lower := (rows 37 98 140 88 273 34 192 128 256), losses := [{ target := 7, region := (rows 5 74 4 8 21 110 64 0 260), good := (rows 309 98 319 122 273 34 98 0 256) }] }

theorem u8001 : Upper (D 7) (R 7) [36,96,136,80,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8002 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 140 88 274 33 65 130 386), lower := (rows 37 98 140 88 274 33 65 128 256), losses := [] }

theorem u8002 : Upper (D 7) (R 7) [36,96,136,80,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8003 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 140 88 274 33 66 129 385), lower := (rows 37 98 140 88 274 33 66 128 256), losses := [] }

theorem u8003 : Upper (D 7) (R 7) [36,96,136,80,258,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8004 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 33, targets := 192 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 140 88 274 33 192 131 259), lower := (rows 37 98 140 88 274 33 192 128 256), losses := [{ target := 0, region := (rows 0 3 4 8 16 32 196 128 256), good := (rows 102 98 204 88 274 34 192 192 256) }] }

theorem u8004 : Upper (D 7) (R 7) [36,96,136,80,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8004 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8005 : Route 9 := (fun mask => (mask,id))

def c8005 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8005 : Upper (D 7) (R 7) [36,96,136,80,384,2,1] 13 := by
  apply FastRouting.sound _ _ [36,96,136,80,384,2,1] 13 (by decide) (choices 1) [1,2] r8005 c8005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u622
  · exact u623

def b8006 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 140 88 400 34 66 129 257), lower := (rows 37 98 140 88 400 34 66 128 256), losses := [] }

theorem u8006 : Upper (D 7) (R 7) [36,96,136,80,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8006 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8007 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 396, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(3,1)], upper := (rows 37 98 140 265 81 34 66 144 400), lower := (rows 37 98 140 265 81 34 66 128 256), losses := [] }

theorem u8007 : Upper (D 7) (R 7) [36,96,136,257,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8008 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 140 265 81 34 80 130 386), lower := (rows 37 98 140 265 81 34 80 128 256), losses := [] }

theorem u8008 : Upper (D 7) (R 7) [36,96,136,257,65,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8008 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8009 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 298, targets := 128 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(1,7),(3,7),(4,1)], upper := (rows 37 98 140 265 81 34 192 146 274), lower := (rows 37 98 140 265 81 34 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 32 196 128 256), good := (rows 117 96 204 281 81 32 192 192 256) }] }

theorem u8009 : Upper (D 7) (R 7) [36,96,136,257,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8010 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 140 265 145 34 66 208 336), lower := (rows 37 98 140 265 145 34 66 128 256), losses := [] }

theorem u8010 : Upper (D 7) (R 7) [36,96,136,257,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8011 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(1,7),(3,7)], upper := (rows 37 98 140 265 145 34 80 194 322), lower := (rows 37 98 140 265 145 34 80 128 256), losses := [] }

theorem u8011 : Upper (D 7) (R 7) [36,96,136,257,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8011 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8012 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 6, region := 178, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 37 98 140 265 146 34 65 208 336), lower := (rows 37 98 140 265 146 34 65 128 256), losses := [] }

theorem u8012 : Upper (D 7) (R 7) [36,96,136,257,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8012 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8013 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 98 140 265 146 34 80 193 321), lower := (rows 37 98 140 265 146 34 80 128 256), losses := [] }

theorem u8013 : Upper (D 7) (R 7) [36,96,136,257,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8013 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8014 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 6, region := 178, targets := 1 }], pairs := [(1,0),(1,7),(3,7)], upper := (rows 37 98 140 265 146 48 65 194 322), lower := (rows 37 98 140 265 146 48 65 128 256), losses := [] }

theorem u8014 : Upper (D 7) (R 7) [36,96,136,257,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8014 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8015 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 98 140 265 146 48 66 193 321), lower := (rows 37 98 140 265 146 48 66 128 256), losses := [] }

theorem u8015 : Upper (D 7) (R 7) [36,96,136,257,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8015 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8016 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 6, region := 178, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 37 98 140 265 208 34 65 146 274), lower := (rows 37 98 140 265 208 34 65 128 256), losses := [] }

theorem u8016 : Upper (D 7) (R 7) [36,96,136,257,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8017 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 140 265 208 34 66 145 273), lower := (rows 37 98 140 265 208 34 66 128 256), losses := [] }

theorem u8017 : Upper (D 7) (R 7) [36,96,136,257,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8018 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 140 265 208 34 80 131 259), lower := (rows 37 98 140 265 208 34 80 128 256), losses := [] }

theorem u8018 : Upper (D 7) (R 7) [36,96,136,257,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8018 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8019 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 396, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 140 266 19 48 65 192 448), lower := (rows 37 98 140 266 19 48 65 128 256), losses := [] }

theorem u8019 : Upper (D 7) (R 7) [36,96,136,258,3,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8019 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8020 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 460, targets := 32 }], pairs := [(1,0),(2,5),(3,5)], upper := (rows 37 98 140 266 19 48 192 193 321), lower := (rows 37 98 140 266 19 48 192 128 256), losses := [{ target := 0, region := (rows 0 3 4 8 16 48 196 128 256), good := (rows 102 98 204 266 50 48 192 192 256) }] }

theorem u8020 : Upper (D 7) (R 7) [36,96,136,258,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8020 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8021 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 140 266 146 33 65 208 336), lower := (rows 37 98 140 266 146 33 65 128 256), losses := [] }

theorem u8021 : Upper (D 7) (R 7) [36,96,136,258,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8021 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8022 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7)], upper := (rows 37 98 140 266 146 33 80 193 321), lower := (rows 37 98 140 266 146 33 80 128 256), losses := [] }

theorem u8022 : Upper (D 7) (R 7) [36,96,136,258,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8022 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8023 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7),(2,5),(3,7)], upper := (rows 37 98 140 266 146 48 65 193 321), lower := (rows 37 98 140 266 146 48 65 128 256), losses := [{ target := 5, region := (rows 1 2 22 10 18 0 65 193 321), good := (rows 453 478 140 286 158 20 449 128 256) }] }

theorem u8023 : Upper (D 7) (R 7) [36,96,136,258,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8023 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8024 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 140 266 208 33 65 146 274), lower := (rows 37 98 140 266 208 33 65 128 256), losses := [] }

theorem u8024 : Upper (D 7) (R 7) [36,96,136,258,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8025 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 140 266 208 33 66 145 273), lower := (rows 37 98 140 266 208 33 66 128 256), losses := [] }

theorem u8025 : Upper (D 7) (R 7) [36,96,136,258,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8026 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 140 266 208 33 80 131 259), lower := (rows 37 98 140 266 208 33 80 128 256), losses := [] }

theorem u8026 : Upper (D 7) (R 7) [36,96,136,258,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8026 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8027 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 115, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,7)], upper := (rows 37 98 140 280 81 34 65 130 386), lower := (rows 37 98 140 280 81 34 65 128 256), losses := [] }

theorem u8027 : Upper (D 7) (R 7) [36,96,136,272,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8028 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 396, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(3,1)], upper := (rows 37 98 140 280 81 34 66 129 385), lower := (rows 37 98 140 280 81 34 66 128 256), losses := [] }

theorem u8028 : Upper (D 7) (R 7) [36,96,136,272,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8029 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 298, targets := 128 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(1,7),(3,7),(4,1)], upper := (rows 37 98 140 280 81 34 192 131 259), lower := (rows 37 98 140 280 81 34 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 32 196 128 256), good := (rows 117 96 204 280 81 32 192 192 256) }] }

theorem u8029 : Upper (D 7) (R 7) [36,96,136,272,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8030 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,5)], upper := (rows 37 98 140 280 146 34 65 193 321), lower := (rows 37 98 140 280 146 34 65 128 256), losses := [{ target := 5, region := (rows 1 2 22 10 18 0 65 193 321), good := (rows 453 478 140 284 158 30 449 128 256) }] }

theorem u8030 : Upper (D 7) (R 7) [36,96,136,272,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8031 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 37 98 140 280 208 34 65 131 259), lower := (rows 37 98 140 280 208 34 65 128 256), losses := [{ target := 7, region := (rows 5 87 4 24 16 127 69 0 325), good := (rows 359 354 367 314 378 34 355 0 256) }] }

theorem u8031 : Upper (D 7) (R 7) [36,96,136,272,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8031 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8032 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 140 280 208 34 66 129 257), lower := (rows 37 98 140 280 208 34 66 128 256), losses := [] }

theorem u8032 : Upper (D 7) (R 7) [36,96,136,272,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8033 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 396, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 140 328 19 48 65 130 386), lower := (rows 37 98 140 328 19 48 65 128 256), losses := [] }

theorem u8033 : Upper (D 7) (R 7) [36,96,136,320,3,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8033 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8034 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 98 140 328 19 48 66 129 385), lower := (rows 37 98 140 328 19 48 66 128 256), losses := [] }

theorem u8034 : Upper (D 7) (R 7) [36,96,136,320,3,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8034 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8035 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 460, targets := 32 }], pairs := [(1,0),(2,5),(3,5)], upper := (rows 37 98 140 328 19 48 192 131 259), lower := (rows 37 98 140 328 19 48 192 128 256), losses := [{ target := 0, region := (rows 0 3 4 8 16 48 196 128 256), good := (rows 102 98 204 328 50 48 192 192 256) }] }

theorem u8035 : Upper (D 7) (R 7) [36,96,136,320,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8035 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8036 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 140 328 146 33 65 146 274), lower := (rows 37 98 140 328 146 33 65 128 256), losses := [] }

theorem u8036 : Upper (D 7) (R 7) [36,96,136,320,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8037 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 140 328 146 33 66 145 273), lower := (rows 37 98 140 328 146 33 66 128 256), losses := [] }

theorem u8037 : Upper (D 7) (R 7) [36,96,136,320,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8037 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8038 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7)], upper := (rows 37 98 140 328 146 33 80 131 259), lower := (rows 37 98 140 328 146 33 80 128 256), losses := [] }

theorem u8038 : Upper (D 7) (R 7) [36,96,136,320,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8038 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8039 : Route 9 := (fun mask => (mask,id))

def c8039 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8039 : Upper (D 7) (R 7) [36,96,136,320,130,16,1] 13 := by
  apply FastRouting.sound _ _ [36,96,136,320,130,16,1] 13 (by decide) (choices 1) [1,2] r8039 c8039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u624
  · exact u625

#print axioms u8039
end Delivery.IrregularNine14.P07
