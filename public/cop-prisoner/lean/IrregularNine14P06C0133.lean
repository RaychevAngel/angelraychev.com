import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0010

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7980 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 297, targets := 4 },{ cop := 2, region := 114, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 82 133 328 52 34 68 131 259), lower := (rows 41 82 133 328 52 34 68 128 256), losses := [] }

theorem u7980 : Upper (D 6) (R 6) [40,80,129,320,36,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7981 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 172, targets := 1 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(2,0),(3,0)], upper := (rows 41 82 164 14 273 96 65 134 262), lower := (rows 41 82 164 14 273 96 65 128 256), losses := [] }

theorem u7981 : Upper (D 6) (R 6) [40,80,160,6,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7982 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 404, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 41 82 164 14 273 96 66 133 261), lower := (rows 41 82 164 14 273 96 66 128 256), losses := [] }

theorem u7982 : Upper (D 6) (R 6) [40,80,160,6,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7982 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7983 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 100, targets := 3 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(2,0),(2,1)], upper := (rows 41 82 164 14 273 96 68 131 259), lower := (rows 41 82 164 14 273 96 68 128 256), losses := [] }

theorem u7983 : Upper (D 6) (R 6) [40,80,160,6,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7983 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7984 : Route 9 := (fun mask => (mask,id))

def c7984 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7984 : Upper (D 6) (R 6) [40,80,160,6,260,64,1] 13 := by
  apply FastRouting.sound _ _ [40,80,160,6,260,64,1] 13 (by decide) (choices 1) [1,2] r7984 c7984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u621
  · exact u622

def b7985 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 404, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 41 82 164 14 276 96 66 129 257), lower := (rows 41 82 164 14 276 96 66 128 256), losses := [] }

theorem u7985 : Upper (D 6) (R 6) [40,80,160,6,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7986 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 420, targets := 65 }], pairs := [(2,0),(2,6)], upper := (rows 41 82 164 73 22 288 65 134 262), lower := (rows 41 82 164 73 22 288 65 128 256), losses := [] }

theorem u7986 : Upper (D 6) (R 6) [40,80,160,65,6,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7986 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7987 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 82, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 41 82 164 73 22 288 66 133 261), lower := (rows 41 82 164 73 22 288 66 128 256), losses := [] }

theorem u7987 : Upper (D 6) (R 6) [40,80,160,65,6,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7987 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7988 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 82, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 41 82 164 73 22 288 68 131 259), lower := (rows 41 82 164 73 22 288 68 128 256), losses := [] }

theorem u7988 : Upper (D 6) (R 6) [40,80,160,65,6,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7988 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7989 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 436, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 41 82 164 73 276 34 65 134 262), lower := (rows 41 82 164 73 276 34 65 128 256), losses := [] }

theorem u7989 : Upper (D 6) (R 6) [40,80,160,65,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7990 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 404, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 41 82 164 73 276 34 66 133 261), lower := (rows 41 82 164 73 276 34 66 128 256), losses := [] }

theorem u7990 : Upper (D 6) (R 6) [40,80,160,65,260,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7990 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7991 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 2, region := 73, targets := 2 }], pairs := [(0,1),(0,2),(3,2)], upper := (rows 41 82 164 73 276 34 68 131 259), lower := (rows 41 82 164 73 276 34 68 128 256), losses := [] }

theorem u7991 : Upper (D 6) (R 6) [40,80,160,65,260,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7991 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7992 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 82, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 41 82 164 76 19 288 65 134 262), lower := (rows 41 82 164 76 19 288 65 128 256), losses := [] }

theorem u7992 : Upper (D 6) (R 6) [40,80,160,68,3,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7992 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7993 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 82, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 41 82 164 76 19 288 66 133 261), lower := (rows 41 82 164 76 19 288 66 128 256), losses := [] }

theorem u7993 : Upper (D 6) (R 6) [40,80,160,68,3,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7993 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7994 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 307, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 41 82 164 76 19 288 68 131 259), lower := (rows 41 82 164 76 19 288 68 128 256), losses := [] }

theorem u7994 : Upper (D 6) (R 6) [40,80,160,68,3,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7994 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7995 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 172, targets := 1 },{ cop := 2, region := 73, targets := 2 }], pairs := [(0,1),(2,0),(3,0)], upper := (rows 41 82 164 76 273 34 65 134 262), lower := (rows 41 82 164 76 273 34 65 128 256), losses := [] }

theorem u7995 : Upper (D 6) (R 6) [40,80,160,68,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7996 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 404, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 41 82 164 76 273 34 66 133 261), lower := (rows 41 82 164 76 273 34 66 128 256), losses := [] }

theorem u7996 : Upper (D 6) (R 6) [40,80,160,68,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7997 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 307, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 41 82 164 76 273 34 68 131 259), lower := (rows 41 82 164 76 273 34 68 128 256), losses := [] }

theorem u7997 : Upper (D 6) (R 6) [40,80,160,68,257,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7997 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7998 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 73, targets := 2 }], pairs := [(0,1),(1,5),(3,1)], upper := (rows 41 82 164 76 276 34 65 131 259), lower := (rows 41 82 164 76 276 34 65 128 256), losses := [{ target := 5, region := (rows 1 11 4 8 24 0 65 193 321), good := (rows 475 466 132 478 276 2 451 128 256) }] }

theorem u7998 : Upper (D 6) (R 6) [40,80,160,68,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7998 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7999 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 404, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 41 82 164 76 276 34 66 129 257), lower := (rows 41 82 164 76 276 34 66 128 256), losses := [] }

theorem u7999 : Upper (D 6) (R 6) [40,80,160,68,260,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7999 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8000 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 397, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 41 82 164 265 19 96 66 132 260), lower := (rows 41 82 164 265 19 96 66 128 256), losses := [] }

theorem u8000 : Upper (D 6) (R 6) [40,80,160,257,3,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8000 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8001 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 7, region := 100, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 41 82 164 265 19 96 68 134 262), lower := (rows 41 82 164 265 19 96 68 128 256), losses := [] }

theorem u8001 : Upper (D 6) (R 6) [40,80,160,257,3,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8001 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8002 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 105, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 82 164 265 22 96 65 134 262), lower := (rows 41 82 164 265 22 96 65 128 256), losses := [] }

theorem u8002 : Upper (D 6) (R 6) [40,80,160,257,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8002 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8003 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 397, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 41 82 164 265 22 96 66 133 261), lower := (rows 41 82 164 265 22 96 66 128 256), losses := [] }

theorem u8003 : Upper (D 6) (R 6) [40,80,160,257,6,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8004 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 118, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 82 164 265 22 96 68 131 259), lower := (rows 41 82 164 265 22 96 68 128 256), losses := [] }

theorem u8004 : Upper (D 6) (R 6) [40,80,160,257,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8004 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8005 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 115, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 41 82 164 268 19 96 65 134 262), lower := (rows 41 82 164 268 19 96 65 128 256), losses := [] }

theorem u8005 : Upper (D 6) (R 6) [40,80,160,260,3,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8005 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8006 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 397, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 41 82 164 268 19 96 66 133 261), lower := (rows 41 82 164 268 19 96 66 128 256), losses := [] }

theorem u8006 : Upper (D 6) (R 6) [40,80,160,260,3,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8006 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8007 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 100, targets := 3 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(2,0),(2,1)], upper := (rows 41 82 164 268 19 96 68 131 259), lower := (rows 41 82 164 268 19 96 68 128 256), losses := [] }

theorem u8007 : Upper (D 6) (R 6) [40,80,160,260,3,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8007 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8008 : Route 9 := (fun mask => (mask,id))

def c8008 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8008 : Upper (D 6) (R 6) [40,80,160,260,6,64,1] 13 := by
  apply FastRouting.sound _ _ [40,80,160,260,6,64,1] 13 (by decide) (choices 1) [1,2] r8008 c8008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u623
  · exact u624

def b8009 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 397, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 41 82 164 268 22 96 66 129 257), lower := (rows 41 82 164 268 22 96 66 128 256), losses := [] }

theorem u8009 : Upper (D 6) (R 6) [40,80,160,260,6,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8009 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8010 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 428, targets := 1 },{ cop := 4, region := 66, targets := 32 }], pairs := [(1,5),(2,0),(3,0)], upper := (rows 41 82 164 328 21 34 65 134 262), lower := (rows 41 82 164 328 21 34 65 128 256), losses := [] }

theorem u8010 : Upper (D 6) (R 6) [40,80,160,320,5,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8010 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8011 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 148, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 41 82 164 328 21 34 66 133 261), lower := (rows 41 82 164 328 21 34 66 128 256), losses := [] }

theorem u8011 : Upper (D 6) (R 6) [40,80,160,320,5,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8012 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 297, targets := 4 },{ cop := 4, region := 66, targets := 32 }], pairs := [(0,2),(1,5),(3,2)], upper := (rows 41 82 164 328 21 34 68 131 259), lower := (rows 41 82 164 328 21 34 68 128 256), losses := [] }

theorem u8012 : Upper (D 6) (R 6) [40,80,160,320,5,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8012 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8013 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 406, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 41 82 388 13 22 33 96 194 322), lower := (rows 41 82 388 13 22 33 96 128 256), losses := [] }

theorem u8013 : Upper (D 6) (R 6) [40,80,384,5,6,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8013 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8014 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 461, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 388 13 22 34 96 193 321), lower := (rows 41 82 388 13 22 34 96 128 256), losses := [] }

theorem u8014 : Upper (D 6) (R 6) [40,80,384,5,6,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8014 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8015 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 2, region := 105, targets := 2 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 41 82 388 13 22 96 96 131 259), lower := (rows 41 82 388 13 22 96 96 128 256), losses := [] }

theorem u8015 : Upper (D 6) (R 6) [40,80,384,5,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8015 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8016 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 436, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 41 82 388 73 52 34 65 134 262), lower := (rows 41 82 388 73 52 34 65 128 256), losses := [] }

theorem u8016 : Upper (D 6) (R 6) [40,80,384,65,36,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8017 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 404, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 41 82 388 73 52 34 66 133 261), lower := (rows 41 82 388 73 52 34 66 128 256), losses := [] }

theorem u8017 : Upper (D 6) (R 6) [40,80,384,65,36,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8017 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8018 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 2, region := 114, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 82 388 73 52 34 68 131 259), lower := (rows 41 82 388 73 52 34 68 128 256), losses := [] }

theorem u8018 : Upper (D 6) (R 6) [40,80,384,65,36,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8019 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 396, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 41 82 388 76 52 33 65 130 258), lower := (rows 41 82 388 76 52 33 65 128 256), losses := [] }

theorem u8019 : Upper (D 6) (R 6) [40,80,384,68,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8019 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8020 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 50, targets := 1 },{ cop := 4, region := 73, targets := 2 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 41 82 388 76 52 34 65 131 259), lower := (rows 41 82 388 76 52 34 65 128 256), losses := [] }

theorem u8020 : Upper (D 6) (R 6) [40,80,384,68,36,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8020 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8021 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 82, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 41 98 133 14 81 288 66 148 276), lower := (rows 41 98 133 14 81 288 66 128 256), losses := [] }

theorem u8021 : Upper (D 6) (R 6) [40,96,129,6,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8021 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8022 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 80, targets := 34 }], pairs := [(4,1),(4,5)], upper := (rows 41 98 133 14 81 288 68 146 274), lower := (rows 41 98 133 14 81 288 68 128 256), losses := [] }

theorem u8022 : Upper (D 6) (R 6) [40,96,129,6,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8022 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8023 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6)], upper := (rows 41 98 133 14 81 288 80 134 262), lower := (rows 41 98 133 14 81 288 80 128 256), losses := [] }

theorem u8023 : Upper (D 6) (R 6) [40,96,129,6,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8023 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8024 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 80, targets := 34 }], pairs := [(4,1),(4,5)], upper := (rows 41 98 133 14 84 288 65 146 274), lower := (rows 41 98 133 14 84 288 65 128 256), losses := [] }

theorem u8024 : Upper (D 6) (R 6) [40,96,129,6,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8024 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8025 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 80, targets := 33 }], pairs := [(4,0),(4,5)], upper := (rows 41 98 133 14 84 288 66 145 273), lower := (rows 41 98 133 14 84 288 66 128 256), losses := [] }

theorem u8025 : Upper (D 6) (R 6) [40,96,129,6,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8025 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8026 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6)], upper := (rows 41 98 133 14 84 288 80 131 259), lower := (rows 41 98 133 14 84 288 80 128 256), losses := [] }

theorem u8026 : Upper (D 6) (R 6) [40,96,129,6,68,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8026 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8027 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 66, targets := 4 }], pairs := [(1,0),(1,2)], upper := (rows 41 98 133 14 276 48 65 194 322), lower := (rows 41 98 133 14 276 48 65 128 256), losses := [{ target := 0, region := (rows 0 66 4 8 24 57 64 194 322), good := (rows 56 482 164 446 308 48 482 128 256) }] }

theorem u8027 : Upper (D 6) (R 6) [40,96,129,6,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8027 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8028 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 41 98 133 14 276 48 66 193 321), lower := (rows 41 98 133 14 276 48 66 128 256), losses := [] }

theorem u8028 : Upper (D 6) (R 6) [40,96,129,6,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8028 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8029 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 0, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 41 98 133 25 274 36 66 196 324), lower := (rows 41 98 133 25 274 36 66 128 256), losses := [] }

theorem u8029 : Upper (D 6) (R 6) [40,96,129,17,258,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8029 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8030 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 133 25 274 36 68 194 322), lower := (rows 41 98 133 25 274 36 68 128 256), losses := [] }

theorem u8030 : Upper (D 6) (R 6) [40,96,129,17,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8030 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8031 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 0, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 41 98 133 25 336 36 66 134 262), lower := (rows 41 98 133 25 336 36 66 128 256), losses := [] }

theorem u8031 : Upper (D 6) (R 6) [40,96,129,17,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8032 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 133 25 336 36 68 130 258), lower := (rows 41 98 133 25 336 36 68 128 256), losses := [] }

theorem u8032 : Upper (D 6) (R 6) [40,96,129,17,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8033 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 66, targets := 1 },{ cop := 0, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 41 98 133 26 273 36 66 196 324), lower := (rows 41 98 133 26 273 36 66 128 256), losses := [{ target := 0, region := (rows 0 39 4 24 16 36 127 164 292), good := (rows 490 482 486 90 346 486 66 128 256) }] }

theorem u8033 : Upper (D 6) (R 6) [40,96,129,18,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8033 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8034 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 133 26 273 36 68 194 322), lower := (rows 41 98 133 26 273 36 68 128 256), losses := [] }

theorem u8034 : Upper (D 6) (R 6) [40,96,129,18,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8035 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 0, region := 66, targets := 4 }], pairs := [(0,6),(1,2),(2,6)], upper := (rows 41 98 133 26 336 36 65 134 262), lower := (rows 41 98 133 26 336 36 65 128 256), losses := [] }

theorem u8035 : Upper (D 6) (R 6) [40,96,129,18,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8035 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8036 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 41 98 133 26 336 36 66 133 261), lower := (rows 41 98 133 26 336 36 66 128 256), losses := [] }

theorem u8036 : Upper (D 6) (R 6) [40,96,129,18,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8036 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8037 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 133 26 336 36 68 131 259), lower := (rows 41 98 133 26 336 36 68 128 256), losses := [] }

theorem u8037 : Upper (D 6) (R 6) [40,96,129,18,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8037 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8038 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 82, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 41 98 133 28 81 288 66 134 262), lower := (rows 41 98 133 28 81 288 66 128 256), losses := [] }

theorem u8038 : Upper (D 6) (R 6) [40,96,129,20,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8038 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8039 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 88, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 41 98 133 28 81 288 68 130 258), lower := (rows 41 98 133 28 81 288 68 128 256), losses := [] }

theorem u8039 : Upper (D 6) (R 6) [40,96,129,20,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8039 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u8039
end Delivery.IrregularNine14.P06
