import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0000

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b60 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 35 76 168 280 36 66 129 260), lower := (rows 19 35 76 168 280 36 66 129 256), losses := [] }

theorem u60 : Upper (D 5) (R 5) [18,33,72,160,264,4,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b60
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b61 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 172, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 35 76 168 280 36 66 132 257), lower := (rows 19 35 76 168 280 36 66 132 256), losses := [] }

theorem u61 : Upper (D 5) (R 5) [18,33,72,160,264,4,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b61
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b62 : PairBound 9 := { available := 32, camps := [{ cop := 6, region := 430, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 196 268 25 40 65 130 288), lower := (rows 19 38 196 268 25 40 65 130 256), losses := [] }

theorem u62 : Upper (D 5) (R 5) [18,36,192,260,9,8,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b62
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b63 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 198, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 196 268 25 40 66 160 257), lower := (rows 19 38 196 268 25 40 66 160 256), losses := [] }

theorem u63 : Upper (D 5) (R 5) [18,36,192,260,9,8,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b63
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b64 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 44 140 304 34 72 129 260), lower := (rows 19 67 44 140 304 34 72 129 256), losses := [] }

theorem u64 : Upper (D 5) (R 5) [18,65,40,132,288,2,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b64
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b65 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 307, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 44 140 304 34 72 132 257), lower := (rows 19 67 44 140 304 34 72 132 256), losses := [] }

theorem u65 : Upper (D 5) (R 5) [18,65,40,132,288,2,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b65
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b66 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 305, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 133 42 276 33 72 136 288), lower := (rows 19 70 133 42 276 33 72 136 256), losses := [] }

theorem u66 : Upper (D 5) (R 5) [18,68,129,34,260,1,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b66
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b67 : PairBound 9 := { available := 8, camps := [{ cop := 0, region := 164, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 70 133 42 276 33 72 160 264), lower := (rows 19 70 133 42 276 33 72 160 256), losses := [] }

theorem u67 : Upper (D 5) (R 5) [18,68,129,34,260,1,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b67
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b68 : PairBound 9 := { available := 8, camps := [{ cop := 1, region := 313, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 70 133 42 304 33 72 132 264), lower := (rows 19 70 133 42 304 33 72 132 256), losses := [] }

theorem u68 : Upper (D 5) (R 5) [18,68,129,34,288,1,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b68
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b69 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 305, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 133 42 304 33 72 136 260), lower := (rows 19 70 133 42 304 33 72 136 256), losses := [] }

theorem u69 : Upper (D 5) (R 5) [18,68,129,34,288,1,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b69
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b70 : PairBound 9 := { available := 32, camps := [{ cop := 7, region := 366, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 134 268 25 40 96 129 288), lower := (rows 19 70 134 268 25 40 96 129 256), losses := [] }

theorem u70 : Upper (D 5) (R 5) [18,68,130,260,9,8,32,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b70
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b71 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 198, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 134 268 25 40 96 160 257), lower := (rows 19 70 134 268 25 40 96 160 256), losses := [] }

theorem u71 : Upper (D 5) (R 5) [18,68,130,260,9,8,32,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b71
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b72 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 140 44 280 34 65 129 288), lower := (rows 19 70 140 44 280 34 65 129 256), losses := [] }

theorem u72 : Upper (D 5) (R 5) [18,68,136,36,264,2,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b72
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b73 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 140, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 140 44 280 34 65 160 257), lower := (rows 19 70 140 44 280 34 65 160 256), losses := [] }

theorem u73 : Upper (D 5) (R 5) [18,68,136,36,264,2,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b73
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b74 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 140 44 304 34 65 129 264), lower := (rows 19 70 140 44 304 34 65 129 256), losses := [] }

theorem u74 : Upper (D 5) (R 5) [18,68,136,36,288,2,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b74
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b75 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 305, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 44 304 34 65 136 257), lower := (rows 19 70 140 44 304 34 65 136 256), losses := [] }

theorem u75 : Upper (D 5) (R 5) [18,68,136,36,288,2,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b75
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b76 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 199, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 140 268 56 33 65 130 288), lower := (rows 19 70 140 268 56 33 65 130 256), losses := [] }

theorem u76 : Upper (D 5) (R 5) [18,68,136,260,40,1,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b76
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b77 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 264, targets := 33 }], pairs := [(3,0),(3,5)], upper := (rows 19 70 140 268 56 33 65 160 258), lower := (rows 19 70 140 268 56 33 65 160 256), losses := [] }

theorem u77 : Upper (D 5) (R 5) [18,68,136,260,40,1,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b77
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b78 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 199, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 140 268 56 34 65 129 288), lower := (rows 19 70 140 268 56 34 65 129 256), losses := [] }

theorem u78 : Upper (D 5) (R 5) [18,68,136,260,40,2,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b78
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b79 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 140 268 56 34 65 160 257), lower := (rows 19 70 140 268 56 34 65 160 256), losses := [] }

theorem u79 : Upper (D 5) (R 5) [18,68,136,260,40,2,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b79
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b80 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 264, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 164 268 56 34 65 129 264), lower := (rows 19 70 164 268 56 34 65 129 256), losses := [] }

theorem u80 : Upper (D 5) (R 5) [18,68,160,260,40,2,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b80
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b81 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 164 268 56 34 65 136 257), lower := (rows 19 70 164 268 56 34 65 136 256), losses := [] }

theorem u81 : Upper (D 5) (R 5) [18,68,160,260,40,2,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b81
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b82 : PairBound 9 := { available := 4, camps := [{ cop := 7, region := 366, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 164 296 25 34 72 129 260), lower := (rows 19 70 164 296 25 34 72 129 256), losses := [] }

theorem u82 : Upper (D 5) (R 5) [18,68,160,288,9,2,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b82
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b83 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 166, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 164 296 25 34 72 132 257), lower := (rows 19 70 164 296 25 34 72 132 256), losses := [] }

theorem u83 : Upper (D 5) (R 5) [18,68,160,288,9,2,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b83
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b84 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 211, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 194 38 268 25 40 65 132 288), lower := (rows 19 194 38 268 25 40 65 132 256), losses := [] }

theorem u84 : Upper (D 5) (R 5) [18,192,34,260,9,8,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b84
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b85 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 198, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 194 38 268 25 40 68 160 257), lower := (rows 19 194 38 268 25 40 68 160 256), losses := [] }

theorem u85 : Upper (D 5) (R 5) [18,192,34,260,9,8,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b85
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b86 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 264, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 194 38 268 56 33 65 136 260), lower := (rows 19 194 38 268 56 33 65 136 256), losses := [] }

theorem u86 : Upper (D 5) (R 5) [18,192,34,260,40,1,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b86
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b87 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 194, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 19 194 38 268 56 33 68 136 257), lower := (rows 19 194 38 268 56 33 68 136 256), losses := [] }

theorem u87 : Upper (D 5) (R 5) [18,192,34,260,40,1,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b87
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b88 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 52 104 400 33 66 140 268), lower := (rows 7 11 52 104 400 33 66 128 256), losses := [] }

theorem u88 : Upper (D 5) (R 5) [6,9,48,96,384,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b88
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b89 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 400, targets := 33 }], pairs := [(4,0),(4,5)], upper := (rows 7 11 52 104 400 33 68 138 266), lower := (rows 7 11 52 104 400 33 68 128 256), losses := [] }

theorem u89 : Upper (D 5) (R 5) [6,9,48,96,384,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b89
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b90 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 437, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 11 52 104 400 33 72 134 262), lower := (rows 7 11 52 104 400 33 72 128 256), losses := [] }

theorem u90 : Upper (D 5) (R 5) [6,9,48,96,384,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b90
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b91 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 308, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 11 52 200 280 33 66 164 292), lower := (rows 7 11 52 200 280 33 66 128 256), losses := [] }

theorem u91 : Upper (D 5) (R 5) [6,9,48,192,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b91
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m92_2 : Upper (D 5) (R 5) [6,9,48,192,264,1,4,2] 13 :=
  permutation_upper _ _ _ [6,9,48,192,264,1,2,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u0

def r92 : Route 9 := (fun mask => (mask,id))

def c92 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u92 : Upper (D 5) (R 5) [6,9,48,192,264,1,4] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,264,1,4] 13 (by decide) (choices 1) [2,32] r92 c92
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m92_2
  · exact u1

def b93 : PairBound 9 := { available := 6, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 11 52 200 280 33 96 134 262), lower := (rows 7 11 52 200 280 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 100 41 51 32 100 129 257), good := (rows 478 410 124 204 280 508 124 128 256) }] }

theorem u93 : Upper (D 5) (R 5) [6,9,48,192,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b93
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b94 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 308, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 11 52 200 280 34 65 164 292), lower := (rows 7 11 52 200 280 34 65 128 256), losses := [] }

theorem u94 : Upper (D 5) (R 5) [6,9,48,192,264,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b94
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m95_1 : Upper (D 5) (R 5) [6,9,48,192,264,2,4,1] 13 :=
  permutation_upper _ _ _ [6,9,48,192,264,2,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2

def r95 : Route 9 := (fun mask => (mask,id))

def c95 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u95 : Upper (D 5) (R 5) [6,9,48,192,264,2,4] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,264,2,4] 13 (by decide) (choices 1) [1,32] r95 c95
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m95_1
  · exact u3

def b96 : PairBound 9 := { available := 5, camps := [], pairs := [(2,1),(3,1)], upper := (rows 7 11 52 200 280 34 96 133 261), lower := (rows 7 11 52 200 280 34 96 128 256), losses := [{ target := 1, region := (rows 1 0 36 9 19 32 100 129 257), good := (rows 477 409 116 200 280 116 100 128 256) }] }

theorem u96 : Upper (D 5) (R 5) [6,9,48,192,264,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b96
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b97 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 71, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 84 168 280 33 66 164 292), lower := (rows 7 11 84 168 280 33 66 128 256), losses := [] }

theorem u97 : Upper (D 5) (R 5) [6,9,80,160,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b97
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b98 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 170, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 11 84 168 280 33 68 162 290), lower := (rows 7 11 84 168 280 33 68 128 256), losses := [] }

theorem u98 : Upper (D 5) (R 5) [6,9,80,160,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b98
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b99 : PairBound 9 := { available := 6, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 11 84 168 280 33 96 134 262), lower := (rows 7 11 84 168 280 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 126 40 50 32 104 131 259), good := (rows 406 478 84 252 348 508 124 128 256) }] }

theorem u99 : Upper (D 5) (R 5) [6,9,80,160,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b99
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b100 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 71, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 84 168 280 34 65 164 292), lower := (rows 7 11 84 168 280 34 65 128 256), losses := [] }

theorem u100 : Upper (D 5) (R 5) [6,9,80,160,264,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b100
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b101 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 170, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 11 84 168 280 34 68 161 289), lower := (rows 7 11 84 168 280 34 68 128 256), losses := [] }

theorem u101 : Upper (D 5) (R 5) [6,9,80,160,264,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b101
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b102 : PairBound 9 := { available := 5, camps := [], pairs := [(2,0),(2,1)], upper := (rows 7 11 84 168 280 34 96 133 261), lower := (rows 7 11 84 168 280 34 96 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 35 107 128 256), good := (rows 102 106 84 232 348 98 96 128 256) },{ target := 1, region := (rows 1 0 126 40 50 32 104 131 259), good := (rows 405 477 84 252 348 508 124 128 256) }] }

theorem u102 : Upper (D 5) (R 5) [6,9,80,160,264,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b102
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b103 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 71, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 84 168 280 36 65 162 290), lower := (rows 7 11 84 168 280 36 65 128 256), losses := [] }

theorem u103 : Upper (D 5) (R 5) [6,9,80,160,264,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b103
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b104 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 71, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 84 168 280 36 66 161 289), lower := (rows 7 11 84 168 280 36 66 128 256), losses := [] }

theorem u104 : Upper (D 5) (R 5) [6,9,80,160,264,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b104
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b105 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 100, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 84 168 280 36 96 131 259), lower := (rows 7 11 84 168 280 36 96 128 256), losses := [] }

theorem u105 : Upper (D 5) (R 5) [6,9,80,160,264,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b105
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b106 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 11 84 168 304 33 66 140 268), lower := (rows 7 11 84 168 304 33 66 128 256), losses := [] }

theorem u106 : Upper (D 5) (R 5) [6,9,80,160,288,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b106
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b107 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 84 168 304 33 68 138 266), lower := (rows 7 11 84 168 304 33 68 128 256), losses := [] }

theorem u107 : Upper (D 5) (R 5) [6,9,80,160,288,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b107
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b108 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 304, targets := 8 }], pairs := [(2,0),(4,3)], upper := (rows 7 11 84 168 304 33 72 134 262), lower := (rows 7 11 84 168 304 33 72 128 256), losses := [{ target := 0, region := (rows 0 2 60 40 48 32 122 131 259), good := (rows 454 462 84 252 380 508 76 128 256) }] }

theorem u108 : Upper (D 5) (R 5) [6,9,80,160,288,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b108
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b109 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 84 168 304 34 65 140 268), lower := (rows 7 11 84 168 304 34 65 128 256), losses := [] }

theorem u109 : Upper (D 5) (R 5) [6,9,80,160,288,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b109
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b110 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 84 168 304 34 68 137 265), lower := (rows 7 11 84 168 304 34 68 128 256), losses := [] }

theorem u110 : Upper (D 5) (R 5) [6,9,80,160,288,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b110
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b111 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 304, targets := 8 }], pairs := [(2,1),(4,3)], upper := (rows 7 11 84 168 304 34 72 133 261), lower := (rows 7 11 84 168 304 34 72 128 256), losses := [{ target := 1, region := (rows 1 0 60 40 48 32 122 131 259), good := (rows 453 461 84 252 380 508 76 128 256) }] }

theorem u111 : Upper (D 5) (R 5) [6,9,80,160,288,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b111
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b112 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 84 168 304 36 65 138 266), lower := (rows 7 11 84 168 304 36 65 128 256), losses := [] }

theorem u112 : Upper (D 5) (R 5) [6,9,80,160,288,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b112
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b113 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 11 84 168 304 36 66 137 265), lower := (rows 7 11 84 168 304 36 66 128 256), losses := [] }

theorem u113 : Upper (D 5) (R 5) [6,9,80,160,288,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b113
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r114 : Route 9 := (fun mask => (mask,id))

def c114 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u114 : Upper (D 5) (R 5) [6,9,80,160,288,4,8] 13 := by
  apply FastRouting.sound _ _ [6,9,80,160,288,4,8] 13 (by decide) (choices 1) [1,2] r114 c114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4
  · exact u5

def b115 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 100 168 273 48 66 140 268), lower := (rows 7 11 100 168 273 48 66 128 256), losses := [] }

theorem u115 : Upper (D 5) (R 5) [6,9,96,160,257,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b115
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b116 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2)], upper := (rows 7 11 100 168 273 48 68 138 266), lower := (rows 7 11 100 168 273 48 68 128 256), losses := [] }

theorem u116 : Upper (D 5) (R 5) [6,9,96,160,257,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b116
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b117 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 68, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 168 273 48 72 134 262), lower := (rows 7 11 100 168 273 48 72 128 256), losses := [] }

theorem u117 : Upper (D 5) (R 5) [6,9,96,160,257,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b117
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b118 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 72, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 19 44 76 152 34 65 416 288), lower := (rows 7 19 44 76 152 34 65 128 256), losses := [] }

theorem u118 : Upper (D 5) (R 5) [6,17,40,68,136,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b118
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b119 : PairBound 9 := { available := 257, camps := [{ cop := 5, region := 76, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 44 76 152 34 96 385 257), lower := (rows 7 19 44 76 152 34 96 128 256), losses := [] }

theorem u119 : Upper (D 5) (R 5) [6,17,40,68,136,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b119
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u119
end Delivery.IrregularNine14.P05
