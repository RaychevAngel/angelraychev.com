import SmallBudgetTenFinite8Profile029Part000

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile29_node131_cert : Bound 8 := { allowed := (rows 144 136 144 0 0 0 0 0), upper := (rows 41 19 76 154 146 178 210 128), lower := (rows 41 19 76 8 16 32 64 128), losses := [] }

theorem profile29_node131 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,72] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,72] 6 146 profile29_node131_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,72] 6 146 profile29_node131_cert).mp (by decide +kernel))

def profile29_node132_cert : Bound 8 := { allowed := (rows 144 136 136 0 0 0 0 0), upper := (rows 41 19 84 138 154 170 202 128), lower := (rows 41 19 84 8 16 32 64 128), losses := [] }

theorem profile29_node132 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,80] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,80] 6 138 profile29_node132_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,80] 6 138 profile29_node132_cert).mp (by decide +kernel))

def profile29_node133_cert : Bound 8 := { allowed := (rows 144 136 24 0 0 0 0 0), upper := (rows 41 19 134 216 216 248 216 128), lower := (rows 41 19 134 8 16 32 64 128), losses := [] }

theorem profile29_node133 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,130] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,130] 6 216 profile29_node133_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,130] 6 216 profile29_node133_cert).mp (by decide +kernel))

def profile29_node134_cert : Bound 8 := { allowed := (rows 144 136 16 0 0 0 0 0), upper := (rows 41 19 140 218 210 242 210 128), lower := (rows 41 19 140 8 16 32 64 128), losses := [] }

theorem profile29_node134 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,136] 6 210 profile29_node134_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,136] 6 210 profile29_node134_cert).mp (by decide +kernel))

def profile29_node135_cert : Bound 8 := { allowed := (rows 144 136 8 0 0 0 0 0), upper := (rows 41 19 148 202 218 234 202 128), lower := (rows 41 19 148 8 16 32 64 128), losses := [] }

theorem profile29_node135 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,144] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,144] 6 202 profile29_node135_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,144] 6 202 profile29_node135_cert).mp (by decide +kernel))

def profile29_node136_cert : Bound 8 := { allowed := (rows 144 136 24 0 0 0 0 0), upper := (rows 41 19 196 154 154 186 218 128), lower := (rows 41 19 196 8 16 32 64 128), losses := [] }

theorem profile29_node136 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,192] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,192] 6 154 profile29_node136_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17,192] 6 154 profile29_node136_cert).mp (by decide +kernel))

def profile29_node124_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 34 => 5 | 40 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile29_node124_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node124 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,17] 6 (by decide) (choices 2) [10,18,24,66,72,80,130,136,144,192] profile29_node124_route profile29_node124_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node125
  · exact profile29_node126
  · exact profile29_node127
  · exact profile29_node128
  · exact profile29_node131
  · exact profile29_node132
  · exact profile29_node133
  · exact profile29_node134
  · exact profile29_node135
  · exact profile29_node136

def profile29_node137_cert : Bound 8 := { allowed := (rows 144 128 152 0 0 0 0 0), upper := (rows 41 26 215 219 211 243 211 128), lower := (rows 41 26 4 8 16 32 64 128), losses := [] }

theorem profile29_node137 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,24] 6 211 profile29_node137_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,24] 6 211 profile29_node137_cert).mp (by decide +kernel))

def profile29_node139_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 41 67 14 152 144 176 208 128), lower := (rows 41 67 14 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 255 255 255 255), good := (rows 243 243 246 240 240 240 240 240) }] }

theorem profile29_node139 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,10] 6 144 profile29_node139_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,10] 6 144 profile29_node139_cert).mp (by decide +kernel))

def profile29_node141_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 41 67 22 24 152 168 200 128), lower := (rows 41 67 22 24 16 32 64 128), losses := [{ target := 4, region := (rows 9 11 4 8 0 41 73 255), good := (rows 235 227 134 235 128 160 192 128) }] }

theorem profile29_node141 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,18,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,18,16] 6 136 profile29_node141_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,18,16] 6 136 profile29_node141_cert).mp (by decide +kernel))

def profile29_node142_cert : CutBound 8 := { lost := (rows 16 0 0 0 0 0 0 0), upper := (rows 41 67 22 136 152 184 216 128), lower := (rows 41 67 22 136 16 32 64 128), losses := [{ target := 4, region := (rows 33 2 4 255 0 32 64 255), good := (rows 169 203 142 136 136 169 200 136) }] }

theorem profile29_node142 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,18,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,18,128] 6 152 profile29_node142_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,18,128] 6 152 profile29_node142_cert).mp (by decide +kernel))

def profile29_node140_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile29_node140_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node140 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,18] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,18] 6 (by decide) (choices 1) [16,128] profile29_node140_route profile29_node140_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node141
  · exact profile29_node142

def profile29_node143_cert : Bound 8 := { allowed := (rows 144 152 128 0 0 0 0 0), upper := (rows 41 67 28 154 146 178 210 128), lower := (rows 41 67 28 8 16 32 64 128), losses := [] }

theorem profile29_node143 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,24] 6 146 profile29_node143_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,24] 6 146 profile29_node143_cert).mp (by decide +kernel))

def profile29_node144_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 41 67 134 152 152 184 216 128), lower := (rows 41 67 134 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 6 0 16 32 64 255), good := (rows 161 199 134 128 144 160 192 128) }] }

theorem profile29_node144 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,130] 6 152 profile29_node144_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,130] 6 152 profile29_node144_cert).mp (by decide +kernel))

def profile29_node145_cert : Bound 8 := { allowed := (rows 144 152 16 0 0 0 0 0), upper := (rows 41 67 140 154 146 178 210 128), lower := (rows 41 67 140 8 16 32 64 128), losses := [] }

theorem profile29_node145 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,136] 6 146 profile29_node145_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,136] 6 146 profile29_node145_cert).mp (by decide +kernel))

def profile29_node146_cert : Bound 8 := { allowed := (rows 144 152 8 0 0 0 0 0), upper := (rows 41 67 148 154 154 186 218 128), lower := (rows 41 67 148 8 16 32 64 128), losses := [] }

theorem profile29_node146 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,144] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,144] 6 154 profile29_node146_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65,144] 6 154 profile29_node146_cert).mp (by decide +kernel))

def profile29_node138_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 34 => 5 | 66 => 6 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 192 => 6 | _ => 0

def profile29_node138_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node138 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,65] 6 (by decide) (choices 2) [10,18,24,130,136,144] profile29_node138_route profile29_node138_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node139
  · exact profile29_node140
  · exact profile29_node143
  · exact profile29_node144
  · exact profile29_node145
  · exact profile29_node146

def profile29_node151_cert : CutBound 8 := { lost := (rows 0 16 16 0 0 0 0 0), upper := (rows 41 74 7 24 144 48 192 128), lower := (rows 41 74 7 24 144 48 64 128), losses := [{ target := 4, region := (rows 1 11 5 8 0 32 255 255), good := (rows 239 202 199 202 192 224 192 192) }] }

theorem profile29_node151 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,3,16,128,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,3,16,128,16] 6 128 profile29_node151_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,3,16,128,16] 6 128 profile29_node151_cert).mp (by decide +kernel))

def profile29_node152_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 41 74 7 24 144 160 80 128), lower := (rows 41 74 7 24 144 160 64 128), losses := [{ target := 4, region := (rows 11 2 6 8 0 255 64 255), good := (rows 169 239 167 169 160 160 224 160) }] }

theorem profile29_node152 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,3,16,128,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,3,16,128,128] 6 16 profile29_node152_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,3,16,128,128] 6 16 profile29_node152_cert).mp (by decide +kernel))

def profile29_node150_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0

def profile29_node150_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node150 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,3,16,128] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,3,16,128] 6 (by decide) (choices 1) [16,128] profile29_node150_route profile29_node150_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node151
  · exact profile29_node152

def profile29_node149_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | _ => 0

def profile29_node149_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node149 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,3,16] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,3,16] 6 (by decide) (choices 1) [128] profile29_node149_route profile29_node149_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile29_node150

def profile29_node153_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 41 74 7 136 144 176 208 128), lower := (rows 41 74 7 136 16 32 64 128), losses := [{ target := 4, region := (rows 33 66 4 255 0 32 64 255), good := (rows 169 202 143 136 136 169 202 136) }] }

theorem profile29_node153 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,3,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,3,128] 6 144 profile29_node153_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,3,128] 6 144 profile29_node153_cert).mp (by decide +kernel))

def profile29_node148_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile29_node148_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node148 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,3] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,3] 6 (by decide) (choices 1) [16,128] profile29_node148_route profile29_node148_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node149
  · exact profile29_node153

def profile29_node154_cert : Bound 8 := { allowed := (rows 144 144 136 0 0 0 0 0), upper := (rows 41 74 21 154 146 178 210 128), lower := (rows 41 74 21 8 16 32 64 128), losses := [] }

theorem profile29_node154 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,17] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,17] 6 146 profile29_node154_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,17] 6 146 profile29_node154_cert).mp (by decide +kernel))

def profile29_node155_cert : Bound 8 := { allowed := (rows 144 144 136 0 0 0 0 0), upper := (rows 41 74 22 153 145 177 209 128), lower := (rows 41 74 22 8 16 32 64 128), losses := [] }

theorem profile29_node155 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,18] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,18] 6 145 profile29_node155_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,18] 6 145 profile29_node155_cert).mp (by decide +kernel))

def profile29_node156_cert : Bound 8 := { allowed := (rows 144 144 24 0 0 0 0 0), upper := (rows 41 74 133 154 146 178 210 128), lower := (rows 41 74 133 8 16 32 64 128), losses := [] }

theorem profile29_node156 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,129] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,129] 6 146 profile29_node156_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,129] 6 146 profile29_node156_cert).mp (by decide +kernel))

def profile29_node157_cert : Bound 8 := { allowed := (rows 144 144 24 0 0 0 0 0), upper := (rows 41 74 134 153 145 177 209 128), lower := (rows 41 74 134 8 16 32 64 128), losses := [] }

theorem profile29_node157 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,130] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,130] 6 145 profile29_node157_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,130] 6 145 profile29_node157_cert).mp (by decide +kernel))

def profile29_node158_cert : Bound 8 := { allowed := (rows 144 144 8 0 0 0 0 0), upper := (rows 41 74 148 155 147 179 211 128), lower := (rows 41 74 148 8 16 32 64 128), losses := [] }

theorem profile29_node158 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,144] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,144] 6 147 profile29_node158_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72,144] 6 147 profile29_node158_cert).mp (by decide +kernel))

def profile29_node147_column : Nat → Fin 8 := fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 10 => 3 | 34 => 5 | 66 => 6 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 192 => 6 | _ => 0

def profile29_node147_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node147 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,72] 6 (by decide) (choices 2) [3,17,18,129,130,144] profile29_node147_route profile29_node147_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node148
  · exact profile29_node154
  · exact profile29_node155
  · exact profile29_node156
  · exact profile29_node157
  · exact profile29_node158

def profile29_node161_cert : CutBound 8 := { lost := (rows 16 0 0 0 0 0 0 0), upper := (rows 41 82 7 24 152 168 200 128), lower := (rows 41 82 7 24 16 32 64 128), losses := [{ target := 4, region := (rows 9 2 4 8 0 41 73 255), good := (rows 233 194 231 233 128 160 192 128) }] }

theorem profile29_node161 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,3,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,3,16] 6 136 profile29_node161_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,3,16] 6 136 profile29_node161_cert).mp (by decide +kernel))

def profile29_node162_cert : CutBound 8 := { lost := (rows 16 0 0 0 0 0 0 0), upper := (rows 41 82 7 136 152 184 216 128), lower := (rows 41 82 7 136 16 32 64 128), losses := [{ target := 4, region := (rows 33 2 4 255 0 32 64 255), good := (rows 169 202 143 136 136 169 200 136) }] }

theorem profile29_node162 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,3,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,3,128] 6 152 profile29_node162_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,3,128] 6 152 profile29_node162_cert).mp (by decide +kernel))

def profile29_node160_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile29_node160_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node160 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,3] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,3] 6 (by decide) (choices 1) [16,128] profile29_node160_route profile29_node160_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node161
  · exact profile29_node162

def profile29_node163_cert : Bound 8 := { allowed := (rows 144 136 144 0 0 0 0 0), upper := (rows 41 82 13 154 146 178 210 128), lower := (rows 41 82 13 8 16 32 64 128), losses := [] }

theorem profile29_node163 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,9] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,9] 6 146 profile29_node163_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,9] 6 146 profile29_node163_cert).mp (by decide +kernel))

def profile29_node164_cert : Bound 8 := { allowed := (rows 144 136 144 0 0 0 0 0), upper := (rows 41 82 14 153 145 177 209 128), lower := (rows 41 82 14 8 16 32 64 128), losses := [] }

theorem profile29_node164 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,10] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,10] 6 145 profile29_node164_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,10] 6 145 profile29_node164_cert).mp (by decide +kernel))

def profile29_node165_cert : Bound 8 := { allowed := (rows 144 136 136 0 0 0 0 0), upper := (rows 41 82 21 138 154 170 202 128), lower := (rows 41 82 21 8 16 32 64 128), losses := [] }

theorem profile29_node165 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,17] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,17] 6 138 profile29_node165_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,17] 6 138 profile29_node165_cert).mp (by decide +kernel))

def profile29_node166_cert : Bound 8 := { allowed := (rows 144 136 136 0 0 0 0 0), upper := (rows 41 82 22 137 153 169 201 128), lower := (rows 41 82 22 8 16 32 64 128), losses := [] }

theorem profile29_node166 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,18] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,18] 6 137 profile29_node166_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,18] 6 137 profile29_node166_cert).mp (by decide +kernel))

def profile29_node167_cert : Bound 8 := { allowed := (rows 144 136 128 0 0 0 0 0), upper := (rows 41 82 28 139 147 163 195 128), lower := (rows 41 82 28 8 16 32 64 128), losses := [] }

theorem profile29_node167 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,24] 6 131 profile29_node167_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,24] 6 131 profile29_node167_cert).mp (by decide +kernel))

def profile29_node168_cert : Bound 8 := { allowed := (rows 144 136 24 0 0 0 0 0), upper := (rows 41 82 133 154 154 186 218 128), lower := (rows 41 82 133 8 16 32 64 128), losses := [] }

theorem profile29_node168 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,129] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,129] 6 154 profile29_node168_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,129] 6 154 profile29_node168_cert).mp (by decide +kernel))

def profile29_node169_cert : Bound 8 := { allowed := (rows 144 136 24 0 0 0 0 0), upper := (rows 41 82 134 153 153 185 217 128), lower := (rows 41 82 134 8 16 32 64 128), losses := [] }

theorem profile29_node169 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,130] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,130] 6 153 profile29_node169_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,130] 6 153 profile29_node169_cert).mp (by decide +kernel))

def profile29_node170_cert : Bound 8 := { allowed := (rows 144 136 16 0 0 0 0 0), upper := (rows 41 82 140 155 147 179 211 128), lower := (rows 41 82 140 8 16 32 64 128), losses := [] }

theorem profile29_node170 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,136] 6 147 profile29_node170_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,136] 6 147 profile29_node170_cert).mp (by decide +kernel))

def profile29_node171_cert : Bound 8 := { allowed := (rows 144 136 8 0 0 0 0 0), upper := (rows 41 82 148 139 155 171 203 128), lower := (rows 41 82 148 8 16 32 64 128), losses := [] }

theorem profile29_node171 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,144] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,144] 6 139 profile29_node171_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80,144] 6 139 profile29_node171_cert).mp (by decide +kernel))

def profile29_node159_column : Nat → Fin 8 := fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 192 => 6 | _ => 0

def profile29_node159_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node159 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,80] 6 (by decide) (choices 2) [3,9,10,17,18,24,129,130,136,144] profile29_node159_route profile29_node159_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node160
  · exact profile29_node163
  · exact profile29_node164
  · exact profile29_node165
  · exact profile29_node166
  · exact profile29_node167
  · exact profile29_node168
  · exact profile29_node169
  · exact profile29_node170
  · exact profile29_node171

def profile29_node172_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 41 131 222 218 218 250 218 128), lower := (rows 41 131 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 64 255), good := (rows 163 131 132 128 144 160 192 128) }] }

theorem profile29_node172 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,129] 6 218 profile29_node172_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,129] 6 218 profile29_node172_cert).mp (by decide +kernel))

def profile29_node173_cert : Bound 8 := { allowed := (rows 144 16 152 0 0 0 0 0), upper := (rows 41 138 215 219 211 243 211 128), lower := (rows 41 138 4 8 16 32 64 128), losses := [] }

theorem profile29_node173 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,136] 6 211 profile29_node173_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,136] 6 211 profile29_node173_cert).mp (by decide +kernel))

def profile29_node174_cert : Bound 8 := { allowed := (rows 144 8 152 0 0 0 0 0), upper := (rows 41 146 223 219 219 251 219 128), lower := (rows 41 146 4 8 16 32 64 128), losses := [] }

theorem profile29_node174 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,144] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,144] 6 219 profile29_node174_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,144] 6 219 profile29_node174_cert).mp (by decide +kernel))

def profile29_node175_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 41 194 159 155 155 187 219 128), lower := (rows 41 194 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 66 4 0 16 32 64 255), good := (rows 161 194 132 128 144 160 194 128) }] }

theorem profile29_node175 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,192] 6 155 profile29_node175_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40,192] 6 155 profile29_node175_cert).mp (by decide +kernel))

def profile29_node122_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 33 => 5 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 40 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | _ => 0

def profile29_node122_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node122 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [40] 6 (by decide) (choices 2) [9,17,24,65,72,80,129,136,144,192] profile29_node122_route profile29_node122_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node123
  · exact profile29_node124
  · exact profile29_node137
  · exact profile29_node138
  · exact profile29_node147
  · exact profile29_node159
  · exact profile29_node172
  · exact profile29_node173
  · exact profile29_node174
  · exact profile29_node175

def profile29_node178_cert : CutBound 8 := { lost := (rows 8 0 0 0 0 0 0 0), upper := (rows 97 11 14 152 144 176 208 128), lower := (rows 97 11 14 8 16 32 64 128), losses := [{ target := 3, region := (rows 255 2 4 0 255 255 255 255), good := (rows 241 243 247 241 241 241 241 241) }] }

theorem profile29_node178 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,10] 6 144 profile29_node178_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,10] 6 144 profile29_node178_cert).mp (by decide +kernel))

def profile29_node180_cert : CutBound 8 := { lost := (rows 16 16 0 0 0 0 0 0), upper := (rows 97 11 22 24 152 168 200 128), lower := (rows 97 11 22 24 16 32 64 128), losses := [{ target := 4, region := (rows 15 10 4 8 0 42 74 255), good := (rows 225 235 231 235 128 160 192 128) }] }

theorem profile29_node180 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,18,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,18,16] 6 136 profile29_node180_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,18,16] 6 136 profile29_node180_cert).mp (by decide +kernel))

def profile29_node181_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 97 11 22 136 152 184 216 128), lower := (rows 97 11 22 136 16 32 64 128), losses := [{ target := 4, region := (rows 1 3 4 255 0 32 64 255), good := (rows 235 139 142 136 136 168 200 136) }] }

theorem profile29_node181 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,18,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,18,128] 6 152 profile29_node181_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,18,128] 6 152 profile29_node181_cert).mp (by decide +kernel))

def profile29_node179_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile29_node179_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node179 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,18] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,18] 6 (by decide) (choices 1) [16,128] profile29_node179_route profile29_node179_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node180
  · exact profile29_node181

def profile29_node182_cert : Bound 8 := { allowed := (rows 152 144 128 0 0 0 0 0), upper := (rows 97 11 28 154 146 178 210 128), lower := (rows 97 11 28 8 16 32 64 128), losses := [] }

theorem profile29_node182 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,24] 6 146 profile29_node182_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,24] 6 146 profile29_node182_cert).mp (by decide +kernel))

def profile29_node183_cert : CutBound 8 := { lost := (rows 0 0 8 0 0 0 0 0), upper := (rows 97 11 134 152 152 184 216 128), lower := (rows 97 11 134 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 2 6 0 16 32 64 255), good := (rows 225 135 134 128 144 160 192 128) }] }

theorem profile29_node183 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,130] 6 152 profile29_node183_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,130] 6 152 profile29_node183_cert).mp (by decide +kernel))

def profile29_node184_cert : Bound 8 := { allowed := (rows 152 144 16 0 0 0 0 0), upper := (rows 97 11 140 154 146 178 210 128), lower := (rows 97 11 140 8 16 32 64 128), losses := [] }

theorem profile29_node184 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,136] 6 146 profile29_node184_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,136] 6 146 profile29_node184_cert).mp (by decide +kernel))

def profile29_node185_cert : Bound 8 := { allowed := (rows 152 144 8 0 0 0 0 0), upper := (rows 97 11 148 154 154 186 218 128), lower := (rows 97 11 148 8 16 32 64 128), losses := [] }

theorem profile29_node185 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,144] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,144] 6 154 profile29_node185_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9,144] 6 154 profile29_node185_cert).mp (by decide +kernel))

def profile29_node177_column : Nat → Fin 8 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 34 => 5 | 66 => 6 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 192 => 6 | _ => 0

def profile29_node177_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node177 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,9] 6 (by decide) (choices 2) [10,18,24,130,136,144] profile29_node177_route profile29_node177_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node178
  · exact profile29_node179
  · exact profile29_node182
  · exact profile29_node183
  · exact profile29_node184
  · exact profile29_node185

def profile29_node188_cert : CutBound 8 := { lost := (rows 16 0 16 0 0 0 0 0), upper := (rows 97 26 7 24 152 168 200 128), lower := (rows 97 26 7 24 16 32 64 128), losses := [{ target := 4, region := (rows 15 2 6 8 0 42 74 255), good := (rows 225 239 231 233 128 160 192 128) }] }

theorem profile29_node188 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,3,16] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,3,16] 6 136 profile29_node188_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,3,16] 6 136 profile29_node188_cert).mp (by decide +kernel))

def profile29_node190_cert : CutBound 8 := { lost := (rows 8 0 8 0 0 0 0 0), upper := (rows 97 26 7 136 24 176 208 128), lower := (rows 97 26 7 136 24 32 64 128), losses := [{ target := 3, region := (rows 23 2 6 0 16 50 82 255), good := (rows 225 247 231 128 241 160 192 128) }] }

theorem profile29_node190 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,3,128,8] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,3,128,8] 6 144 profile29_node190_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,3,128,8] 6 144 profile29_node190_cert).mp (by decide +kernel))

def profile29_node191_cert : CutBound 8 := { lost := (rows 128 0 128 0 0 0 0 0), upper := (rows 97 26 7 136 144 56 88 128), lower := (rows 97 26 7 136 144 32 64 128), losses := [{ target := 7, region := (rows 7 2 6 8 16 34 66 0), good := (rows 97 127 103 8 16 32 64 0) }] }

theorem profile29_node191 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,3,128,128] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,3,128,128] 6 24 profile29_node191_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,3,128,128] 6 24 profile29_node191_cert).mp (by decide +kernel))

def profile29_node189_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile29_node189_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node189 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,3,128] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,3,128] 6 (by decide) (choices 1) [8,128] profile29_node189_route profile29_node189_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node190
  · exact profile29_node191

def profile29_node187_column : Nat → Fin 8 := fun mask => match mask with | 1 => 0 | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0

def profile29_node187_route : Route 8 := (fun mask => (mask,id))

theorem profile29_node187 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,3] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,3] 6 (by decide) (choices 1) [16,128] profile29_node187_route profile29_node187_column
    (by change RowCover 8 1 (choices 1); exact cover ⟨1,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile29_node188
  · exact profile29_node189

def profile29_node192_cert : Bound 8 := { allowed := (rows 152 128 144 0 0 0 0 0), upper := (rows 97 26 13 154 146 178 210 128), lower := (rows 97 26 13 8 16 32 64 128), losses := [] }

theorem profile29_node192 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,9] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,9] 6 146 profile29_node192_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,9] 6 146 profile29_node192_cert).mp (by decide +kernel))

def profile29_node193_cert : Bound 8 := { allowed := (rows 152 128 144 0 0 0 0 0), upper := (rows 97 26 14 153 145 177 209 128), lower := (rows 97 26 14 8 16 32 64 128), losses := [] }

theorem profile29_node193 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,10] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,10] 6 145 profile29_node193_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,10] 6 145 profile29_node193_cert).mp (by decide +kernel))

def profile29_node194_cert : Bound 8 := { allowed := (rows 152 128 128 0 0 0 0 0), upper := (rows 97 26 28 139 147 163 195 128), lower := (rows 97 26 28 8 16 32 64 128), losses := [] }

theorem profile29_node194 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,24] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,24] 6 131 profile29_node194_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,24] 6 131 profile29_node194_cert).mp (by decide +kernel))

def profile29_node195_cert : Bound 8 := { allowed := (rows 152 128 24 0 0 0 0 0), upper := (rows 97 26 133 154 154 186 218 128), lower := (rows 97 26 133 8 16 32 64 128), losses := [] }

theorem profile29_node195 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,129] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,129] 6 154 profile29_node195_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,129] 6 154 profile29_node195_cert).mp (by decide +kernel))

def profile29_node196_cert : Bound 8 := { allowed := (rows 152 128 24 0 0 0 0 0), upper := (rows 97 26 134 153 153 185 217 128), lower := (rows 97 26 134 8 16 32 64 128), losses := [] }

theorem profile29_node196 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,130] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,130] 6 153 profile29_node196_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,130] 6 153 profile29_node196_cert).mp (by decide +kernel))

def profile29_node197_cert : Bound 8 := { allowed := (rows 152 128 16 0 0 0 0 0), upper := (rows 97 26 140 155 147 179 211 128), lower := (rows 97 26 140 8 16 32 64 128), losses := [] }

theorem profile29_node197 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,136] 6 :=
  DegreeLoss.bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,136] 6 147 profile29_node197_cert
    ((DegreeLoss.boundCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24,136] 6 147 profile29_node197_cert).mp (by decide +kernel))

def profile29_node186_column : Nat → Fin 8 := fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 192 => 6 | _ => 0

def profile29_node186_route : Route 8 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile29_node186 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,24] 6 (by decide) (choices 2) [3,9,10,24,129,130,136] profile29_node186_route profile29_node186_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node187
  · exact profile29_node192
  · exact profile29_node193
  · exact profile29_node194
  · exact profile29_node195
  · exact profile29_node196
  · exact profile29_node197

def profile29_node198_cert : CutBound 8 := { lost := (rows 0 8 0 0 0 0 0 0), upper := (rows 97 131 158 154 154 186 218 128), lower := (rows 97 131 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 64 255), good := (rows 227 131 132 128 144 160 192 128) }] }

theorem profile29_node198 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,129] 6 154 profile29_node198_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,129] 6 154 profile29_node198_cert).mp (by decide +kernel))

def profile29_node199_cert : CutBound 8 := { lost := (rows 0 16 0 0 0 0 0 0), upper := (rows 97 138 159 155 155 187 219 128), lower := (rows 97 138 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 10 4 8 0 32 64 255), good := (rows 225 138 132 138 128 160 192 128) }] }

theorem profile29_node199 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,136] 6 155 profile29_node199_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96,136] 6 155 profile29_node199_cert).mp (by decide +kernel))

def profile29_node176_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 192 => 6 | _ => 0

def profile29_node176_route : Route 8 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

theorem profile29_node176 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [96] 6 (by decide) (choices 2) [9,24,129,136] profile29_node176_route profile29_node176_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile29_node177
  · exact profile29_node186
  · exact profile29_node198
  · exact profile29_node199

def profile29_node200_cert : CutBound 8 := { lost := (rows 8 0 0 0 0 0 0 0), upper := (rows 131 251 253 249 249 249 249 128), lower := (rows 131 2 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 3 2 4 0 16 32 64 255), good := (rows 131 131 132 128 144 160 192 128) }] }

theorem profile29_node200 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [130] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [130] 6 249 profile29_node200_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [130] 6 249 profile29_node200_cert).mp (by decide +kernel))

def profile29_node201_cert : CutBound 8 := { lost := (rows 16 0 0 0 0 0 0 0), upper := (rows 137 251 255 251 251 251 251 128), lower := (rows 137 2 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 9 2 4 8 0 32 64 255), good := (rows 137 130 132 137 128 160 192 128) }] }

theorem profile29_node201 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [136] 6 251 profile29_node201_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [136] 6 251 profile29_node201_cert).mp (by decide +kernel))

def profile29_node202_cert : CutBound 8 := { lost := (rows 8 0 0 0 0 0 0 0), upper := (rows 161 219 223 219 219 251 219 128), lower := (rows 161 2 4 8 16 32 64 128), losses := [{ target := 3, region := (rows 33 2 4 0 16 32 64 255), good := (rows 161 130 132 128 144 161 192 128) }] }

theorem profile29_node202 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [160] 6 219 profile29_node202_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [160] 6 219 profile29_node202_cert).mp (by decide +kernel))

def profile29_node0_column : Nat → Fin 8 := fun mask => match mask with | 6 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | _ => 0

def profile29_node0_route : Route 8 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile29_node0 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [] 6 (by decide) (choices 2) [10,24,34,40,96,130,136,160] profile29_node0_route profile29_node0_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile29_node1
  · exact profile29_node50
  · exact profile29_node81
  · exact profile29_node122
  · exact profile29_node176
  · exact profile29_node200
  · exact profile29_node201
  · exact profile29_node202

theorem profile29 : Upper (D (n:=8) [33,33,32,18,18,17,17,2]) (R (n:=8) [33,33,32,18,18,17,17,2]) [] 6 := profile29_node0


#print axioms profile29
end Delivery.SmallBudgetTenFinite8
