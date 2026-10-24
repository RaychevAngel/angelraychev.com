import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0032
import IrregularNine14P03C0033

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5100 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 44 88 208 165 197 133 389), lower := (rows 259 35 44 88 208 32 64 128 256), losses := [] }

theorem u5100 : Upper (D 3) (R 3) [258,33,40,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5100
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5101 : Route 9 := (fun mask => (mask,id))

def c5101 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5101 : Upper (D 3) (R 3) [258,33,40,192,65] 13 := by
  apply FastRouting.sound _ _ [258,33,40,192,65] 13 (by decide) (choices 1) [1,4,16,128] r5101 c5101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1972
  · exact u1973
  · exact u1974
  · exact u1975

def b5102 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 44 200 84 177 209 145 401), lower := (rows 259 35 44 200 84 32 64 128 256), losses := [] }

theorem u5102 : Upper (D 3) (R 3) [258,33,40,192,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5102
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5103 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 35 44 200 208 53 85 149 277), lower := (rows 259 35 44 200 208 32 64 128 256), losses := [] }

theorem u5103 : Upper (D 3) (R 3) [258,33,40,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5103
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5104 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 35 69 73 148 184 248 184 440), lower := (rows 259 35 69 73 148 32 64 128 256), losses := [] }

theorem u5104 : Upper (D 3) (R 3) [258,33,65,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5104
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5105 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 35 69 73 176 188 220 156 412), lower := (rows 259 35 69 73 176 32 64 128 256), losses := [] }

theorem u5105 : Upper (D 3) (R 3) [258,33,65,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5105
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5106 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 69 76 145 184 248 184 440), lower := (rows 259 35 69 76 145 32 64 128 256), losses := [] }

theorem u5106 : Upper (D 3) (R 3) [258,33,65,68,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5106
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5107 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 69 76 152 177 241 177 433), lower := (rows 259 35 69 76 152 32 64 128 256), losses := [] }

theorem u5107 : Upper (D 3) (R 3) [258,33,65,68,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5107
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5108 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 69 76 176 185 217 153 409), lower := (rows 259 35 69 76 176 32 64 128 256), losses := [] }

theorem u5108 : Upper (D 3) (R 3) [258,33,65,68,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5108
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5109 : Route 9 := (fun mask => (mask,id))

def c5109 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5109 : Upper (D 3) (R 3) [258,33,65,80,129] 13 := by
  apply FastRouting.sound _ _ [258,33,65,80,129] 13 (by decide) (choices 1) [4,8,128] r5109 c5109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1976
  · exact u1977
  · exact u1978

def b5110 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 69 88 148 169 233 169 425), lower := (rows 259 35 69 88 148 32 64 128 256), losses := [] }

theorem u5110 : Upper (D 3) (R 3) [258,33,65,80,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5110
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5111 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 69 88 152 165 229 165 421), lower := (rows 259 35 69 88 152 32 64 128 256), losses := [] }

theorem u5111 : Upper (D 3) (R 3) [258,33,65,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5111
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5112 : Route 9 := (fun mask => (mask,id))

def c5112 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5112 : Upper (D 3) (R 3) [258,33,65,80,160] 13 := by
  apply FastRouting.sound _ _ [258,33,65,80,160] 13 (by decide) (choices 1) [1,4,8,128] r5112 c5112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1979
  · exact u1980
  · exact u1981
  · exact u1982

def r5113 : Route 9 := (fun mask => (mask,id))

def c5113 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5113 : Upper (D 3) (R 3) [258,33,65,96,129] 13 := by
  apply FastRouting.sound _ _ [258,33,65,96,129] 13 (by decide) (choices 1) [4,8,16,128] r5113 c5113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1983
  · exact u1984
  · exact u1985
  · exact u1986

def r5114 : Route 9 := (fun mask => (mask,id))

def c5114 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5114 : Upper (D 3) (R 3) [258,33,65,96,132] 13 := by
  apply FastRouting.sound _ _ [258,33,65,96,132] 13 (by decide) (choices 1) [1,8,16,128] r5114 c5114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1987
  · exact u1988
  · exact u1989
  · exact u1990

def r5115 : Route 9 := (fun mask => (mask,id))

def c5115 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5115 : Upper (D 3) (R 3) [258,33,65,96,136] 13 := by
  apply FastRouting.sound _ _ [258,33,65,96,136] 13 (by decide) (choices 1) [1,4,16,128] r5115 c5115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1991
  · exact u1992
  · exact u1993
  · exact u1994

theorem m5116_8 : Upper (D 3) (R 3) [258,33,65,129,192,8] 13 :=
  permutation_upper _ _ _ [258,33,65,129,192,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1995

def r5116 : Route 9 := (fun mask => (mask,id))

def c5116 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5116 : Upper (D 3) (R 3) [258,33,65,129,192] 13 := by
  apply FastRouting.sound _ _ [258,33,65,129,192] 13 (by decide) (choices 1) [4,8,16] r5116 c5116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1995
  · exact m5116_8
  · exact u1996

def b5117 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 35 69 140 152 113 113 241 369), lower := (rows 259 35 69 140 152 32 64 128 256), losses := [] }

theorem u5117 : Upper (D 3) (R 3) [258,33,65,132,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5117
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5118 : Route 9 := (fun mask => (mask,id))

def c5118 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5118 : Upper (D 3) (R 3) [258,33,65,132,160] 13 := by
  apply FastRouting.sound _ _ [258,33,65,132,160] 13 (by decide) (choices 1) [1,8,16,64] r5118 c5118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1997
  · exact u1998
  · exact u1999
  · exact u2000

def r5119 : Route 9 := (fun mask => (mask,id))

def c5119 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5119 : Upper (D 3) (R 3) [258,33,65,132,192] 13 := by
  apply FastRouting.sound _ _ [258,33,65,132,192] 13 (by decide) (choices 1) [1,8,16] r5119 c5119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2001
  · exact u2002
  · exact u2003

def b5120 : PairBound 9 := { available := 101, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 69 152 152 101 101 229 357), lower := (rows 259 35 69 152 152 32 64 128 256), losses := [] }

theorem u5120 : Upper (D 3) (R 3) [258,33,65,144,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5120
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5121 : PairBound 9 := { available := 77, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 35 69 152 176 109 77 205 333), lower := (rows 259 35 69 152 176 32 64 128 256), losses := [] }

theorem u5121 : Upper (D 3) (R 3) [258,33,65,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5121
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5122 : PairBound 9 := { available := 45, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 35 69 152 208 45 109 173 301), lower := (rows 259 35 69 152 208 32 64 128 256), losses := [] }

theorem u5122 : Upper (D 3) (R 3) [258,33,65,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5122
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5123 : Route 9 := (fun mask => (mask,id))

def c5123 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5123 : Upper (D 3) (R 3) [258,33,65,160,192] 13 := by
  apply FastRouting.sound _ _ [258,33,65,160,192] 13 (by decide) (choices 1) [1,4,8,16] r5123 c5123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2004
  · exact u2005
  · exact u2006
  · exact u2007

def b5124 : PairBound 9 := { available := 145, camps := [{ cop := 6, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 76 76 176 177 209 145 401), lower := (rows 259 35 76 76 176 32 64 128 256), losses := [] }

theorem u5124 : Upper (D 3) (R 3) [258,33,72,68,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5124
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5125 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 76 88 148 161 225 161 417), lower := (rows 259 35 76 88 148 32 64 128 256), losses := [] }

theorem u5125 : Upper (D 3) (R 3) [258,33,72,80,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5125
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5126 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 76 88 176 165 197 133 389), lower := (rows 259 35 76 88 176 32 64 128 256), losses := [] }

theorem u5126 : Upper (D 3) (R 3) [258,33,72,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5126
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5127 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 76 104 148 177 209 145 401), lower := (rows 259 35 76 104 148 32 64 128 256), losses := [] }

theorem u5127 : Upper (D 3) (R 3) [258,33,72,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5127
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5128 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 76 140 112 177 209 145 401), lower := (rows 259 35 76 140 112 32 64 128 256), losses := [] }

theorem u5128 : Upper (D 3) (R 3) [258,33,72,132,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5128
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5129 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 76 140 208 49 113 177 305), lower := (rows 259 35 76 140 208 32 64 128 256), losses := [] }

theorem u5129 : Upper (D 3) (R 3) [258,33,72,132,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5129
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5130 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 76 152 112 165 197 133 389), lower := (rows 259 35 76 152 112 32 64 128 256), losses := [] }

theorem u5130 : Upper (D 3) (R 3) [258,33,72,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5130
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5131 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 76 152 208 37 101 165 293), lower := (rows 259 35 76 152 208 32 64 128 256), losses := [] }

theorem u5131 : Upper (D 3) (R 3) [258,33,72,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5131
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5132 : Route 9 := (fun mask => (mask,id))

def c5132 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5132 : Upper (D 3) (R 3) [258,33,72,160,192] 13 := by
  apply FastRouting.sound _ _ [258,33,72,160,192] 13 (by decide) (choices 1) [1,4,16] r5132 c5132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2008
  · exact u2009
  · exact u2010

def b5133 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 76 200 176 53 85 149 277), lower := (rows 259 35 76 200 176 32 64 128 256), losses := [] }

theorem u5133 : Upper (D 3) (R 3) [258,33,72,192,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5133
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5134 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 13 88 49 225 193 193 449), lower := (rows 259 38 13 88 49 32 64 128 256), losses := [] }

theorem u5134 : Upper (D 3) (R 3) [258,36,9,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5134
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5135 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 13 88 81 161 225 161 417), lower := (rows 259 38 13 88 81 32 64 128 256), losses := [] }

theorem u5135 : Upper (D 3) (R 3) [258,36,9,80,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5135
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5136 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 13 88 112 161 193 129 385), lower := (rows 259 38 13 88 112 32 64 128 256), losses := [] }

theorem u5136 : Upper (D 3) (R 3) [258,36,9,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5136
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5137 : Route 9 := (fun mask => (mask,id))

def c5137 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5137 : Upper (D 3) (R 3) [258,36,9,80,129] 13 := by
  apply FastRouting.sound _ _ [258,36,9,80,129] 13 (by decide) (choices 1) [1,64,128] r5137 c5137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2011
  · exact u2012
  · exact u2013

def b5138 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 38 13 88 176 225 193 193 449), lower := (rows 259 38 13 88 176 32 64 128 256), losses := [] }

theorem u5138 : Upper (D 3) (R 3) [258,36,9,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5138
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5139 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 13 88 208 161 225 161 417), lower := (rows 259 38 13 88 208 32 64 128 256), losses := [] }

theorem u5139 : Upper (D 3) (R 3) [258,36,9,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5139
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5140 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 13 200 49 241 209 209 465), lower := (rows 259 38 13 200 49 32 64 128 256), losses := [] }

theorem u5140 : Upper (D 3) (R 3) [258,36,9,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5140
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5141 : Route 9 := (fun mask => (mask,id))

def c5141 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5141 : Upper (D 3) (R 3) [258,36,9,192,65] 13 := by
  apply FastRouting.sound _ _ [258,36,9,192,65] 13 (by decide) (choices 1) [1,16,128] r5141 c5141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2014
  · exact u2015
  · exact u2016

def r5142 : Route 9 := (fun mask => (mask,id))

def c5142 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5142 : Upper (D 3) (R 3) [258,36,9,192,96] 13 := by
  apply FastRouting.sound _ _ [258,36,9,192,96] 13 (by decide) (choices 1) [1,16,128] r5142 c5142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2017
  · exact u2018
  · exact u2019

def b5143 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 13 200 208 49 113 177 305), lower := (rows 259 38 13 200 208 32 64 128 256), losses := [] }

theorem u5143 : Upper (D 3) (R 3) [258,36,9,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5143
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5144 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 38 28 41 81 225 193 193 449), lower := (rows 259 38 28 41 81 32 64 128 256), losses := [] }

theorem u5144 : Upper (D 3) (R 3) [258,36,24,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5144
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5145 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 38 28 41 208 225 193 193 449), lower := (rows 259 38 28 41 208 32 64 128 256), losses := [] }

theorem u5145 : Upper (D 3) (R 3) [258,36,24,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5145
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5146 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 28 73 81 161 225 161 417), lower := (rows 259 38 28 73 81 32 64 128 256), losses := [] }

theorem u5146 : Upper (D 3) (R 3) [258,36,24,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5146
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5147 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 385, targets := 32 }], pairs := [(0,5)], upper := (rows 259 38 28 73 112 161 193 129 385), lower := (rows 259 38 28 73 112 32 64 128 256), losses := [] }

theorem u5147 : Upper (D 3) (R 3) [258,36,24,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5147
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5148_128 : Upper (D 3) (R 3) [258,36,24,65,129,128] 13 :=
  permutation_upper _ _ _ [258,36,24,65,129,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2021

def r5148 : Route 9 := (fun mask => (mask,id))

def c5148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5148 : Upper (D 3) (R 3) [258,36,24,65,129] 13 := by
  apply FastRouting.sound _ _ [258,36,24,65,129] 13 (by decide) (choices 1) [1,64,128] r5148 c5148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2020
  · exact u2021
  · exact m5148_128

def b5149 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 38 28 73 176 225 193 193 449), lower := (rows 259 38 28 73 176 32 64 128 256), losses := [] }

theorem u5149 : Upper (D 3) (R 3) [258,36,24,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5149
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5150 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 28 73 208 161 225 161 417), lower := (rows 259 38 28 73 208 32 64 128 256), losses := [] }

theorem u5150 : Upper (D 3) (R 3) [258,36,24,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5150
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5151 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 385, targets := 32 }], pairs := [(0,5)], upper := (rows 259 38 28 104 208 161 193 129 385), lower := (rows 259 38 28 104 208 32 64 128 256), losses := [] }

theorem u5151 : Upper (D 3) (R 3) [258,36,24,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5151
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5152 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 259 38 28 200 208 33 97 161 289), lower := (rows 259 38 28 200 208 32 64 128 256), losses := [] }

theorem u5152 : Upper (D 3) (R 3) [258,36,24,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5152
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5153 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 259 38 69 25 25 224 224 224 480), lower := (rows 259 38 69 25 25 32 64 128 256), losses := [] }

theorem u5153 : Upper (D 3) (R 3) [258,36,65,17,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5153
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5154 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 69 25 49 232 200 200 456), lower := (rows 259 38 69 25 49 32 64 128 256), losses := [] }

theorem u5154 : Upper (D 3) (R 3) [258,36,65,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5154
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5155 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 38 69 25 56 225 193 193 449), lower := (rows 259 38 69 25 56 32 64 128 256), losses := [] }

theorem u5155 : Upper (D 3) (R 3) [258,36,65,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5155
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5156 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 259 38 69 25 81 168 232 168 424), lower := (rows 259 38 69 25 81 32 64 128 256), losses := [] }

theorem u5156 : Upper (D 3) (R 3) [258,36,65,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5156
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5157 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 259 38 69 25 88 161 225 161 417), lower := (rows 259 38 69 25 88 32 64 128 256), losses := [] }

theorem u5157 : Upper (D 3) (R 3) [258,36,65,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5157
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5158 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 196, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 69 25 112 169 201 137 393), lower := (rows 259 38 69 25 112 32 64 128 256), losses := [] }

theorem u5158 : Upper (D 3) (R 3) [258,36,65,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5158
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5159 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 38 69 25 145 232 232 232 488), lower := (rows 259 38 69 25 145 32 64 128 256), losses := [] }

theorem u5159 : Upper (D 3) (R 3) [258,36,65,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5159
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u5159
end Delivery.IrregularNine14.P03
