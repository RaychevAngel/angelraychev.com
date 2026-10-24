import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile3_node1_cert : CutBound 8 := { lost := (rows 128 0 0 0 0 0 0 0), upper := (rows 113 227 229 233 241 32 64 128), lower := (rows 113 2 4 8 16 32 64 128), losses := [{ target := 7, region := (rows 17 2 4 8 16 255 255 0), good := (rows 113 98 100 104 113 96 96 96) }] }

theorem profile3_node1 : Upper (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [112] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [112] 6 225 profile3_node1_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [112] 6 225 profile3_node1_cert).mp (by decide +kernel))

def profile3_node4_cert : CutBound 8 := { lost := (rows 0 32 0 32 0 0 0 0), upper := (rows 225 19 37 201 209 32 64 128), lower := (rows 225 19 37 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 7 4 15 23 0 255 255), good := (rows 219 219 223 200 208 192 192 192) }] }

theorem profile3_node4 : Upper (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [224,17,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [224,17,33] 6 193 profile3_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [224,17,33] 6 193 profile3_node4_cert).mp (by decide +kernel))

def profile3_node5_cert : CutBound 8 := { lost := (rows 0 0 1 0 0 0 0 0), upper := (rows 225 19 100 137 145 32 64 128), lower := (rows 225 19 100 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 2 255 8 16 255 255 255), good := (rows 228 246 228 236 244 228 228 228) }] }

theorem profile3_node5 : Upper (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [224,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [224,17,96] 6 129 profile3_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [224,17,96] 6 129 profile3_node5_cert).mp (by decide +kernel))

def profile3_node3_column : Nat → Fin 8 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile3_node3_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile3_node3 : Upper (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [224,17] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [224,17] 6 (by decide) (choices 2) [33,96] profile3_node3_route profile3_node3_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile3_node4
  · exact profile3_node5

def profile3_node6_cert : CutBound 8 := { lost := (rows 0 0 32 32 0 0 0 0), upper := (rows 225 35 213 217 209 32 64 128), lower := (rows 225 35 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 7 11 19 0 255 255), good := (rows 221 223 196 200 208 192 192 192) }] }

theorem profile3_node6 : Upper (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [224,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [224,33] 6 209 profile3_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [224,33] 6 209 profile3_node6_cert).mp (by decide +kernel))

def profile3_node7_cert : CutBound 8 := { lost := (rows 0 1 0 0 0 0 0 0), upper := (rows 225 50 197 201 209 32 64 128), lower := (rows 225 50 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 18 4 8 16 255 255 255), good := (rows 224 242 228 232 242 224 224 224) }] }

theorem profile3_node7 : Upper (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [224,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [224,48] 6 193 profile3_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [224,48] 6 193 profile3_node7_cert).mp (by decide +kernel))

def profile3_node8_cert : CutBound 8 := { lost := (rows 0 1 0 0 0 0 0 0), upper := (rows 225 98 149 153 145 32 64 128), lower := (rows 225 98 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) }] }

theorem profile3_node8 : Upper (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [224,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [224,96] 6 145 profile3_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [224,96] 6 145 profile3_node8_cert).mp (by decide +kernel))

def profile3_node2_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | _ => 0

def profile3_node2_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile3_node2 : Upper (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [224] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [224] 6 (by decide) (choices 2) [17,33,48,96] profile3_node2_route profile3_node2_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile3_node3
  · exact profile3_node6
  · exact profile3_node7
  · exact profile3_node8

def profile3_node0_column : Nat → Fin 8 := fun mask => match mask with | 14 => 1 | 22 => 1 | 38 => 1 | 70 => 1 | 134 => 1 | 26 => 1 | 42 => 1 | 74 => 1 | 138 => 1 | 50 => 1 | 82 => 1 | 146 => 1 | 98 => 1 | 162 => 1 | 194 => 1 | 28 => 2 | 44 => 2 | 76 => 2 | 140 => 2 | 52 => 2 | 84 => 2 | 148 => 2 | 100 => 2 | 164 => 2 | 196 => 2 | 56 => 3 | 88 => 3 | 152 => 3 | 104 => 3 | 168 => 3 | 200 => 3 | _ => 0

def profile3_node0_route : Route 8 := (fun mask => match mask with | 176 => (112,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 208 => (112,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile3_node0 : Upper (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [] 6 (by decide) (choices 3) [112,224] profile3_node0_route profile3_node0_column
    (by change RowCover 8 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile3_node1
  · exact profile3_node2

theorem profile3 : Upper (D (n:=8) [51,32,32,32,17,2,2,2]) (R (n:=8) [51,32,32,32,17,2,2,2]) [] 6 := profile3_node0


#print axioms profile3
end Delivery.SmallBudgetTenFinite8
