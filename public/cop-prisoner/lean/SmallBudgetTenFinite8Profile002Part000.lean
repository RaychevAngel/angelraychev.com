import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile2_node1_cert : CutBound 8 := { lost := (rows 192 0 0 0 0 0 0 0), upper := (rows 51 243 245 249 16 32 64 128), lower := (rows 51 2 4 8 16 32 64 128), losses := [{ target := 6, region := (rows 3 2 4 8 255 255 0 255), good := (rows 179 179 180 184 176 176 176 176) },{ target := 7, region := (rows 3 2 4 8 255 255 255 0), good := (rows 115 115 116 120 112 112 112 112) }] }

theorem profile2_node1 : Upper (D (n:=8) [49,49,32,32,2,2,2,2]) (R (n:=8) [49,49,32,32,2,2,2,2]) [50] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,49,32,32,2,2,2,2]) (R (n:=8) [49,49,32,32,2,2,2,2]) [50] 6 241 profile2_node1_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,49,32,32,2,2,2,2]) (R (n:=8) [49,49,32,32,2,2,2,2]) [50] 6 241 profile2_node1_cert).mp (by decide +kernel))

def profile2_node3_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 113 51 198 202 16 32 64 128), lower := (rows 113 51 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 10 0 255 255 255), good := (rows 225 239 228 232 224 224 224 224) }] }

theorem profile2_node3 : Upper (D (n:=8) [49,49,32,32,2,2,2,2]) (R (n:=8) [49,49,32,32,2,2,2,2]) [112,49] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,49,32,32,2,2,2,2]) (R (n:=8) [49,49,32,32,2,2,2,2]) [112,49] 6 194 profile2_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,49,32,32,2,2,2,2]) (R (n:=8) [49,49,32,32,2,2,2,2]) [112,49] 6 194 profile2_node3_cert).mp (by decide +kernel))

def profile2_node4_cert : CutBound 8 := { lost := (rows 128 128 0 0 0 0 0 0), upper := (rows 113 114 135 139 16 32 64 128), lower := (rows 113 114 4 8 16 32 64 128), losses := [{ target := 7, region := (rows 255 255 4 8 255 255 255 0), good := (rows 115 115 119 123 115 115 115 115) }] }

theorem profile2_node4 : Upper (D (n:=8) [49,49,32,32,2,2,2,2]) (R (n:=8) [49,49,32,32,2,2,2,2]) [112,112] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,49,32,32,2,2,2,2]) (R (n:=8) [49,49,32,32,2,2,2,2]) [112,112] 6 131 profile2_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,49,32,32,2,2,2,2]) (R (n:=8) [49,49,32,32,2,2,2,2]) [112,112] 6 131 profile2_node4_cert).mp (by decide +kernel))

def profile2_node5_cert : CutBound 8 := { lost := (rows 0 0 16 16 0 0 0 0), upper := (rows 113 147 230 234 16 32 64 128), lower := (rows 113 147 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 6 10 0 255 255 255), good := (rows 225 239 228 232 224 224 224 224) }] }

theorem profile2_node5 : Upper (D (n:=8) [49,49,32,32,2,2,2,2]) (R (n:=8) [49,49,32,32,2,2,2,2]) [112,145] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,49,32,32,2,2,2,2]) (R (n:=8) [49,49,32,32,2,2,2,2]) [112,145] 6 226 profile2_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,49,32,32,2,2,2,2]) (R (n:=8) [49,49,32,32,2,2,2,2]) [112,145] 6 226 profile2_node5_cert).mp (by decide +kernel))

def profile2_node6_cert : CutBound 8 := { lost := (rows 128 64 0 0 0 0 0 0), upper := (rows 113 178 199 203 16 32 64 128), lower := (rows 113 178 4 8 16 32 64 128), losses := [{ target := 6, region := (rows 1 255 4 8 255 255 0 255), good := (rows 179 178 182 186 178 178 178 178) },{ target := 7, region := (rows 255 2 4 8 255 255 255 0), good := (rows 113 115 117 121 113 113 113 113) }] }

theorem profile2_node6 : Upper (D (n:=8) [49,49,32,32,2,2,2,2]) (R (n:=8) [49,49,32,32,2,2,2,2]) [112,176] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [49,49,32,32,2,2,2,2]) (R (n:=8) [49,49,32,32,2,2,2,2]) [112,176] 6 195 profile2_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [49,49,32,32,2,2,2,2]) (R (n:=8) [49,49,32,32,2,2,2,2]) [112,176] 6 195 profile2_node6_cert).mp (by decide +kernel))

def profile2_node2_column : Nat → Fin 8 := fun mask => match mask with | 13 => 2 | 21 => 2 | 37 => 2 | 69 => 2 | 133 => 2 | 25 => 3 | 41 => 3 | 73 => 3 | 137 => 3 | 28 => 2 | 44 => 2 | 76 => 2 | 140 => 2 | 52 => 2 | 84 => 2 | 148 => 2 | 100 => 2 | 164 => 2 | 196 => 2 | 56 => 3 | 88 => 3 | 152 => 3 | 104 => 3 | 168 => 3 | 200 => 3 | _ => 0

def profile2_node2_route : Route 8 := (fun mask => match mask with | 81 => (49,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 97 => (49,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 161 => (145,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 193 => (145,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 208 => (176,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 224 => (176,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

theorem profile2_node2 : Upper (D (n:=8) [49,49,32,32,2,2,2,2]) (R (n:=8) [49,49,32,32,2,2,2,2]) [112] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,49,32,32,2,2,2,2]) (R (n:=8) [49,49,32,32,2,2,2,2]) [112] 6 (by decide) (choices 3) [49,112,145,176] profile2_node2_route profile2_node2_column
    (by change RowCover 8 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile2_node3
  · exact profile2_node4
  · exact profile2_node5
  · exact profile2_node6

def profile2_node0_column : Nat → Fin 8 := fun mask => match mask with | 14 => 2 | 22 => 2 | 38 => 2 | 70 => 2 | 134 => 2 | 26 => 3 | 42 => 3 | 74 => 3 | 138 => 3 | 28 => 2 | 44 => 2 | 76 => 2 | 140 => 2 | 52 => 2 | 84 => 2 | 148 => 2 | 100 => 2 | 164 => 2 | 196 => 2 | 56 => 3 | 88 => 3 | 152 => 3 | 104 => 3 | 168 => 3 | 200 => 3 | _ => 0

def profile2_node0_route : Route 8 := (fun mask => match mask with | 82 => (50,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 146 => (50,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 98 => (50,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 162 => (50,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 194 => (50,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | 176 => (112,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 208 => (112,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 224 => (112,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | _ => (mask,id))

theorem profile2_node0 : Upper (D (n:=8) [49,49,32,32,2,2,2,2]) (R (n:=8) [49,49,32,32,2,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [49,49,32,32,2,2,2,2]) (R (n:=8) [49,49,32,32,2,2,2,2]) [] 6 (by decide) (choices 3) [50,112] profile2_node0_route profile2_node0_column
    (by change RowCover 8 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile2_node1
  · exact profile2_node2

theorem profile2 : Upper (D (n:=8) [49,49,32,32,2,2,2,2]) (R (n:=8) [49,49,32,32,2,2,2,2]) [] 6 := profile2_node0


#print axioms profile2
end Delivery.SmallBudgetTenFinite8
