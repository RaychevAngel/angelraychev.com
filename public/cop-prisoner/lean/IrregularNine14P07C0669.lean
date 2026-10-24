import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0477
import IrregularNine14P07C0478

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b40140 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 12, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 97 259 28 140 176 99 67 195 323), lower := (rows 97 259 28 140 176 32 64 128 256), losses := [] }

theorem u40140 : Upper (D 7) (R 7) [96,257,24,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40140 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40141 : Route 9 := (fun mask => (mask,id))

def c40141 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40141 : Upper (D 7) (R 7) [96,257,24,160,192] 13 := by
  apply FastRouting.sound _ _ [96,257,24,160,192] 13 (by decide) (choices 1) [1,2,4] r40141 c40141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28626
  · exact u28627
  · exact u28628

def b40142 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 97 259 37 74 146 188 220 156 412), lower := (rows 97 259 37 74 146 32 64 128 256), losses := [] }

theorem u40142 : Upper (D 7) (R 7) [96,257,33,66,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40143 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 97 259 37 74 148 186 218 154 410), lower := (rows 97 259 37 74 148 32 64 128 256), losses := [] }

theorem u40143 : Upper (D 7) (R 7) [96,257,33,66,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40143 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40144 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 97 259 37 74 152 182 214 150 406), lower := (rows 97 259 37 74 152 32 64 128 256), losses := [] }

theorem u40144 : Upper (D 7) (R 7) [96,257,33,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40145 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 12, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 259 37 76 146 186 218 154 410), lower := (rows 97 259 37 76 146 32 64 128 256), losses := [] }

theorem u40145 : Upper (D 7) (R 7) [96,257,33,68,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40146 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 12, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 259 37 76 152 178 210 146 402), lower := (rows 97 259 37 76 152 32 64 128 256), losses := [] }

theorem u40146 : Upper (D 7) (R 7) [96,257,33,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40147 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 97 259 37 88 146 174 206 142 398), lower := (rows 97 259 37 88 146 32 64 128 256), losses := [] }

theorem u40147 : Upper (D 7) (R 7) [96,257,33,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40147 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40148 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 97 259 37 88 148 170 202 138 394), lower := (rows 97 259 37 88 148 32 64 128 256), losses := [] }

theorem u40148 : Upper (D 7) (R 7) [96,257,33,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40149 : PairBound 9 := { available := 134, camps := [{ cop := 2, region := 474, targets := 32 },{ cop := 0, region := 4, targets := 2 }], pairs := [(1,5),(2,1),(3,5),(4,5)], upper := (rows 97 259 37 88 152 166 198 134 390), lower := (rows 97 259 37 88 152 32 64 128 256), losses := [] }

theorem u40149 : Upper (D 7) (R 7) [96,257,33,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40150 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 97 259 37 138 148 122 90 218 346), lower := (rows 97 259 37 138 148 32 64 128 256), losses := [] }

theorem u40150 : Upper (D 7) (R 7) [96,257,33,130,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40150 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40151 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 97 259 37 138 208 62 94 158 286), lower := (rows 97 259 37 138 208 32 64 128 256), losses := [] }

theorem u40151 : Upper (D 7) (R 7) [96,257,33,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40152 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 97 259 37 140 208 58 90 154 282), lower := (rows 97 259 37 140 208 32 64 128 256), losses := [] }

theorem u40152 : Upper (D 7) (R 7) [96,257,33,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40153 : Route 9 := (fun mask => (mask,id))

def c40153 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40153 : Upper (D 7) (R 7) [96,257,34,66,129] 13 := by
  apply FastRouting.sound _ _ [96,257,34,66,129] 13 (by decide) (choices 1) [4,8,16,128] r40153 c40153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28629
  · exact u28630
  · exact u28631
  · exact u28632

def r40154 : Route 9 := (fun mask => (mask,id))

def c40154 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40154 : Upper (D 7) (R 7) [96,257,34,66,132] 13 := by
  apply FastRouting.sound _ _ [96,257,34,66,132] 13 (by decide) (choices 1) [1,8,16,128] r40154 c40154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28633
  · exact u28634
  · exact u28635
  · exact u28636

def r40155 : Route 9 := (fun mask => (mask,id))

def c40155 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40155 : Upper (D 7) (R 7) [96,257,34,68,129] 13 := by
  apply FastRouting.sound _ _ [96,257,34,68,129] 13 (by decide) (choices 1) [2,8,16,128] r40155 c40155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28637
  · exact u28638
  · exact u28639
  · exact u28640

def r40156 : Route 9 := (fun mask => (mask,id))

def c40156 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40156 : Upper (D 7) (R 7) [96,257,34,68,130] 13 := by
  apply FastRouting.sound _ _ [96,257,34,68,130] 13 (by decide) (choices 1) [1,8,16,128] r40156 c40156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28641
  · exact u28642
  · exact u28643
  · exact u28644

def r40157 : Route 9 := (fun mask => (mask,id))

def c40157 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40157 : Upper (D 7) (R 7) [96,257,34,68,136] 13 := by
  apply FastRouting.sound _ _ [96,257,34,68,136] 13 (by decide) (choices 1) [1,2,16,128] r40157 c40157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28645
  · exact u28646
  · exact u28647
  · exact u28648

def r40158 : Route 9 := (fun mask => (mask,id))

def c40158 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40158 : Upper (D 7) (R 7) [96,257,34,80,129] 13 := by
  apply FastRouting.sound _ _ [96,257,34,80,129] 13 (by decide) (choices 1) [2,4,8,128] r40158 c40158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28649
  · exact u28650
  · exact u28651
  · exact u28652

def r40159 : Route 9 := (fun mask => (mask,id))

def c40159 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40159 : Upper (D 7) (R 7) [96,257,34,80,130] 13 := by
  apply FastRouting.sound _ _ [96,257,34,80,130] 13 (by decide) (choices 1) [1,4,8,128] r40159 c40159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28653
  · exact u28654
  · exact u28655
  · exact u28656

def r40160 : Route 9 := (fun mask => (mask,id))

def c40160 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40160 : Upper (D 7) (R 7) [96,257,34,80,132] 13 := by
  apply FastRouting.sound _ _ [96,257,34,80,132] 13 (by decide) (choices 1) [1,2,8,128] r40160 c40160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28657
  · exact u28658
  · exact u28659
  · exact u28660

def r40161 : Route 9 := (fun mask => (mask,id))

def c40161 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40161 : Upper (D 7) (R 7) [96,257,34,80,136] 13 := by
  apply FastRouting.sound _ _ [96,257,34,80,136] 13 (by decide) (choices 1) [1,2,4,128] r40161 c40161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28661
  · exact u28662
  · exact u28663
  · exact u28664

def r40162 : Route 9 := (fun mask => (mask,id))

def c40162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40162 : Upper (D 7) (R 7) [96,257,34,129,130] 13 := by
  apply FastRouting.sound _ _ [96,257,34,129,130] 13 (by decide) (choices 1) [4,8,16,64] r40162 c40162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28665
  · exact u28666
  · exact u28667
  · exact u28668

def r40163 : Route 9 := (fun mask => (mask,id))

def c40163 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40163 : Upper (D 7) (R 7) [96,257,34,129,132] 13 := by
  apply FastRouting.sound _ _ [96,257,34,129,132] 13 (by decide) (choices 1) [2,8,16,64] r40163 c40163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28669
  · exact u28670
  · exact u28671
  · exact u28672

def b40164 : PairBound 9 := { available := 86, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 97 259 38 137 152 118 86 214 342), lower := (rows 97 259 38 137 152 32 64 128 256), losses := [] }

theorem u40164 : Upper (D 7) (R 7) [96,257,34,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40164 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40165 : Route 9 := (fun mask => (mask,id))

def c40165 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40165 : Upper (D 7) (R 7) [96,257,34,129,192] 13 := by
  apply FastRouting.sound _ _ [96,257,34,129,192] 13 (by decide) (choices 1) [2,4,8,16] r40165 c40165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28673
  · exact u28674
  · exact u28675
  · exact u28676

def r40166 : Route 9 := (fun mask => (mask,id))

def c40166 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40166 : Upper (D 7) (R 7) [96,257,34,130,132] 13 := by
  apply FastRouting.sound _ _ [96,257,34,130,132] 13 (by decide) (choices 1) [1,8,16,64] r40166 c40166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28677
  · exact u28678
  · exact u28679
  · exact u28680

def b40167 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 97 259 38 138 152 117 85 213 341), lower := (rows 97 259 38 138 152 32 64 128 256), losses := [] }

theorem u40167 : Upper (D 7) (R 7) [96,257,34,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40167 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40168 : Route 9 := (fun mask => (mask,id))

def c40168 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40168 : Upper (D 7) (R 7) [96,257,34,130,192] 13 := by
  apply FastRouting.sound _ _ [96,257,34,130,192] 13 (by decide) (choices 1) [1,4,8,16] r40168 c40168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28681
  · exact u28682
  · exact u28683
  · exact u28684

def b40169 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 97 259 38 140 152 115 83 211 339), lower := (rows 97 259 38 140 152 32 64 128 256), losses := [] }

theorem u40169 : Upper (D 7) (R 7) [96,257,34,132,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40170 : Route 9 := (fun mask => (mask,id))

def c40170 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40170 : Upper (D 7) (R 7) [96,257,34,132,192] 13 := by
  apply FastRouting.sound _ _ [96,257,34,132,192] 13 (by decide) (choices 1) [1,2,8,16] r40170 c40170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28685
  · exact u28686
  · exact u28687
  · exact u28688

def b40171 : PairBound 9 := { available := 71, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 259 38 152 152 103 71 199 327), lower := (rows 97 259 38 152 152 32 64 128 256), losses := [] }

theorem u40171 : Upper (D 7) (R 7) [96,257,34,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40172 : PairBound 9 := { available := 15, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 259 38 152 208 47 79 143 271), lower := (rows 97 259 38 152 208 32 64 128 256), losses := [] }

theorem u40172 : Upper (D 7) (R 7) [96,257,34,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40173 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 12, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 259 44 76 145 178 210 146 402), lower := (rows 97 259 44 76 145 32 64 128 256), losses := [] }

theorem u40173 : Upper (D 7) (R 7) [96,257,40,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40174 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 12, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 259 44 76 146 179 211 147 403), lower := (rows 97 259 44 76 146 32 64 128 256), losses := [] }

theorem u40174 : Upper (D 7) (R 7) [96,257,40,68,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40175 : Route 9 := (fun mask => (mask,id))

def c40175 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40175 : Upper (D 7) (R 7) [96,257,40,80,129] 13 := by
  apply FastRouting.sound _ _ [96,257,40,80,129] 13 (by decide) (choices 1) [2,4,128] r40175 c40175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28689
  · exact u28690
  · exact u28691

def r40176 : Route 9 := (fun mask => (mask,id))

def c40176 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40176 : Upper (D 7) (R 7) [96,257,40,80,130] 13 := by
  apply FastRouting.sound _ _ [96,257,40,80,130] 13 (by decide) (choices 1) [1,2,4,128] r40176 c40176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28692
  · exact u28693
  · exact u28694
  · exact u28695

def r40177 : Route 9 := (fun mask => (mask,id))

def c40177 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40177 : Upper (D 7) (R 7) [96,257,40,80,132] 13 := by
  apply FastRouting.sound _ _ [96,257,40,80,132] 13 (by decide) (choices 1) [1,2,128] r40177 c40177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28696
  · exact u28697
  · exact u28698

def r40178 : Route 9 := (fun mask => (mask,id))

def c40178 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40178 : Upper (D 7) (R 7) [96,257,40,129,130] 13 := by
  apply FastRouting.sound _ _ [96,257,40,129,130] 13 (by decide) (choices 1) [2,4,16,64] r40178 c40178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28699
  · exact u28700
  · exact u28701
  · exact u28702

def r40179 : Route 9 := (fun mask => (mask,id))

def c40179 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40179 : Upper (D 7) (R 7) [96,257,40,129,132] 13 := by
  apply FastRouting.sound _ _ [96,257,40,129,132] 13 (by decide) (choices 1) [2,16,64] r40179 c40179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28703
  · exact u28704
  · exact u28705

def r40180 : Route 9 := (fun mask => (mask,id))

def c40180 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40180 : Upper (D 7) (R 7) [96,257,40,129,192] 13 := by
  apply FastRouting.sound _ _ [96,257,40,129,192] 13 (by decide) (choices 1) [2,4,16] r40180 c40180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28706
  · exact u28707
  · exact u28708

def r40181 : Route 9 := (fun mask => (mask,id))

def c40181 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40181 : Upper (D 7) (R 7) [96,257,40,130,129] 13 := by
  apply FastRouting.sound _ _ [96,257,40,130,129] 13 (by decide) (choices 1) [2,4,16,64] r40181 c40181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28709
  · exact u28710
  · exact u28711
  · exact u28712

def b40182 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 97 259 44 138 146 117 85 213 341), lower := (rows 97 259 44 138 146 32 64 128 256), losses := [] }

theorem u40182 : Upper (D 7) (R 7) [96,257,40,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40182 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40183 : Route 9 := (fun mask => (mask,id))

def c40183 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40183 : Upper (D 7) (R 7) [96,257,40,130,132] 13 := by
  apply FastRouting.sound _ _ [96,257,40,130,132] 13 (by decide) (choices 1) [1,2,16,64] r40183 c40183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28713
  · exact u28714
  · exact u28715
  · exact u28716

def r40184 : Route 9 := (fun mask => (mask,id))

def c40184 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40184 : Upper (D 7) (R 7) [96,257,40,130,192] 13 := by
  apply FastRouting.sound _ _ [96,257,40,130,192] 13 (by decide) (choices 1) [1,2,4,16] r40184 c40184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28717
  · exact u28718
  · exact u28719
  · exact u28720

def b40185 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(4,5)], upper := (rows 97 259 44 140 145 114 82 210 338), lower := (rows 97 259 44 140 145 32 64 128 256), losses := [] }

theorem u40185 : Upper (D 7) (R 7) [96,257,40,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40185 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40186 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(4,5)], upper := (rows 97 259 44 140 146 115 83 211 339), lower := (rows 97 259 44 140 146 32 64 128 256), losses := [] }

theorem u40186 : Upper (D 7) (R 7) [96,257,40,132,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40186 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40187 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(4,5)], upper := (rows 97 259 44 140 208 51 83 147 275), lower := (rows 97 259 44 140 208 32 64 128 256), losses := [] }

theorem u40187 : Upper (D 7) (R 7) [96,257,40,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40188 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 259 44 152 145 102 70 198 326), lower := (rows 97 259 44 152 145 32 64 128 256), losses := [] }

theorem u40188 : Upper (D 7) (R 7) [96,257,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40188 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40189 : PairBound 9 := { available := 71, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 259 44 152 146 103 71 199 327), lower := (rows 97 259 44 152 146 32 64 128 256), losses := [] }

theorem u40189 : Upper (D 7) (R 7) [96,257,40,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40189 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40190 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 259 44 152 148 99 67 195 323), lower := (rows 97 259 44 152 148 32 64 128 256), losses := [] }

theorem u40190 : Upper (D 7) (R 7) [96,257,40,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40190 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40191 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 259 44 152 208 39 71 135 263), lower := (rows 97 259 44 152 208 32 64 128 256), losses := [] }

theorem u40191 : Upper (D 7) (R 7) [96,257,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40191 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40192 : Route 9 := (fun mask => (mask,id))

def c40192 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40192 : Upper (D 7) (R 7) [96,257,40,192,129] 13 := by
  apply FastRouting.sound _ _ [96,257,40,192,129] 13 (by decide) (choices 1) [2,4,16] r40192 c40192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28721
  · exact u28722
  · exact u28723

def r40193 : Route 9 := (fun mask => (mask,id))

def c40193 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40193 : Upper (D 7) (R 7) [96,257,40,192,130] 13 := by
  apply FastRouting.sound _ _ [96,257,40,192,130] 13 (by decide) (choices 1) [1,2,4,16] r40193 c40193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28724
  · exact u28725
  · exact u28726
  · exact u28727

def r40194 : Route 9 := (fun mask => (mask,id))

def c40194 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40194 : Upper (D 7) (R 7) [96,257,40,192,132] 13 := by
  apply FastRouting.sound _ _ [96,257,40,192,132] 13 (by decide) (choices 1) [1,2,16] r40194 c40194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28728
  · exact u28729
  · exact u28730

def b40195 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 4, targets := 130 },{ cop := 2, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 259 100 137 146 62 94 158 286), lower := (rows 97 259 100 137 146 32 64 128 256), losses := [] }

theorem u40195 : Upper (D 7) (R 7) [96,257,96,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40196 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 4, targets := 130 },{ cop := 2, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 259 100 137 148 58 90 154 282), lower := (rows 97 259 100 137 148 32 64 128 256), losses := [] }

theorem u40196 : Upper (D 7) (R 7) [96,257,96,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40197 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 4, targets := 130 },{ cop := 2, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 259 100 138 148 59 91 155 283), lower := (rows 97 259 100 138 148 32 64 128 256), losses := [] }

theorem u40197 : Upper (D 7) (R 7) [96,257,96,130,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40198 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 8, targets := 224 },{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5),(3,5),(3,6),(3,7)], upper := (rows 97 262 7 11 56 240 208 208 464), lower := (rows 97 262 7 11 56 32 64 128 256), losses := [] }

theorem u40198 : Upper (D 7) (R 7) [96,260,3,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40198 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40199 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 8, targets := 224 },{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5),(3,5),(3,6),(3,7)], upper := (rows 97 262 7 11 152 240 240 240 496), lower := (rows 97 262 7 11 152 32 64 128 256), losses := [] }

theorem u40199 : Upper (D 7) (R 7) [96,260,3,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40199 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u40199
end Delivery.IrregularNine14.P07
