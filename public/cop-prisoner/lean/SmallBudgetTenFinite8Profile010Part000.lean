import SmallBudgetTenFinite8Common

namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile10_node2_cert : CutBound 8 := { lost := (rows 0 0 32 32 32 0 0 0), upper := (rows 97 35 197 201 209 32 64 128), lower := (rows 97 35 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 7 11 19 0 255 255), good := (rows 221 223 196 200 208 192 192 192) }] }

theorem profile10_node2 : Upper (D (n:=8) [36,32,32,32,32,2,2,2]) (R (n:=8) [36,32,32,32,32,2,2,2]) [96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [36,32,32,32,32,2,2,2]) (R (n:=8) [36,32,32,32,32,2,2,2]) [96,33] 6 193 profile10_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [36,32,32,32,32,2,2,2]) (R (n:=8) [36,32,32,32,32,2,2,2]) [96,33] 6 193 profile10_node2_cert).mp (by decide +kernel))

def profile10_node3_cert : CutBound 8 := { lost := (rows 0 1 32 32 32 0 0 0), upper := (rows 97 98 133 137 145 32 64 128), lower := (rows 97 98 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 221 194 196 200 208 192 192 192) }] }

theorem profile10_node3 : Upper (D (n:=8) [36,32,32,32,32,2,2,2]) (R (n:=8) [36,32,32,32,32,2,2,2]) [96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [36,32,32,32,32,2,2,2]) (R (n:=8) [36,32,32,32,32,2,2,2]) [96,96] 6 129 profile10_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [36,32,32,32,32,2,2,2]) (R (n:=8) [36,32,32,32,32,2,2,2]) [96,96] 6 129 profile10_node3_cert).mp (by decide +kernel))

def profile10_node4_cert : CutBound 8 := { lost := (rows 128 96 0 0 0 0 0 0), upper := (rows 97 131 229 233 241 32 64 128), lower := (rows 97 131 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 255 255), good := (rows 195 195 196 200 208 192 192 192) },{ target := 6, region := (rows 1 3 4 8 16 255 0 255), good := (rows 163 163 164 168 176 160 160 160) },{ target := 7, region := (rows 255 2 4 8 16 255 255 0), good := (rows 97 99 101 105 113 97 97 97) }] }

theorem profile10_node4 : Upper (D (n:=8) [36,32,32,32,32,2,2,2]) (R (n:=8) [36,32,32,32,32,2,2,2]) [96,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [36,32,32,32,32,2,2,2]) (R (n:=8) [36,32,32,32,32,2,2,2]) [96,129] 6 225 profile10_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [36,32,32,32,32,2,2,2]) (R (n:=8) [36,32,32,32,32,2,2,2]) [96,129] 6 225 profile10_node4_cert).mp (by decide +kernel))

def profile10_node5_cert : CutBound 8 := { lost := (rows 0 1 32 32 32 0 0 0), upper := (rows 97 162 197 201 209 32 64 128), lower := (rows 97 162 4 8 16 32 64 128), losses := [{ target := 0, region := (rows 0 255 4 8 16 255 255 255), good := (rows 226 226 230 234 242 226 226 226) },{ target := 5, region := (rows 1 2 5 9 17 0 255 255), good := (rows 221 194 196 200 208 192 192 192) }] }

theorem profile10_node5 : Upper (D (n:=8) [36,32,32,32,32,2,2,2]) (R (n:=8) [36,32,32,32,32,2,2,2]) [96,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=8) [36,32,32,32,32,2,2,2]) (R (n:=8) [36,32,32,32,32,2,2,2]) [96,160] 6 193 profile10_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=8) [36,32,32,32,32,2,2,2]) (R (n:=8) [36,32,32,32,32,2,2,2]) [96,160] 6 193 profile10_node5_cert).mp (by decide +kernel))

def profile10_node1_column : Nat → Fin 8 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile10_node1_route : Route 8 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile10_node1 : Upper (D (n:=8) [36,32,32,32,32,2,2,2]) (R (n:=8) [36,32,32,32,32,2,2,2]) [96] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [36,32,32,32,32,2,2,2]) (R (n:=8) [36,32,32,32,32,2,2,2]) [96] 6 (by decide) (choices 2) [33,96,129,160] profile10_node1_route profile10_node1_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile10_node2
  · exact profile10_node3
  · exact profile10_node4
  · exact profile10_node5

def profile10_node0_column : Nat → Fin 8 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | _ => 0

def profile10_node0_route : Route 8 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile10_node0 : Upper (D (n:=8) [36,32,32,32,32,2,2,2]) (R (n:=8) [36,32,32,32,32,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=8) [36,32,32,32,32,2,2,2]) (R (n:=8) [36,32,32,32,32,2,2,2]) [] 6 (by decide) (choices 2) [96] profile10_node0_route profile10_node0_column
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile10_node1

theorem profile10 : Upper (D (n:=8) [36,32,32,32,32,2,2,2]) (R (n:=8) [36,32,32,32,32,2,2,2]) [] 6 := profile10_node0


#print axioms profile10
end Delivery.SmallBudgetTenFinite8
