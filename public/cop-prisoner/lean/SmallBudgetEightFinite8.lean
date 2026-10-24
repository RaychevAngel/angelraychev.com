import SmallRowPrefixCut
import SmallBudgetProfiles

/-! Complete row-prefix coverage for every sorted joint-degree profile on
8 vertices with 8 arrows and the stated degree restriction. -/
namespace Delivery.SmallBudgetEightFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rows (a b c d e f g h : Nat) : Rows 8 := fun v =>
  match v.val with | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | 6 => g | _ => h

def choices (d : Nat) : List Nat :=
  match d with
  | 0 => [0]
  | 1 => [1,2,4,8,16,32,64,128]
  | 2 => [3,5,9,17,33,65,129,6,10,18,34,66,130,12,20,36,68,132,24,40,72,136,48,80,144,96,160,192]
  | 3 => [7,11,19,35,67,131,13,21,37,69,133,25,41,73,137,49,81,145,97,161,193,14,22,38,70,134,26,42,74,138,50,82,146,98,162,194,28,44,76,140,52,84,148,100,164,196,56,88,152,104,168,200,112,176,208,224]
  | 4 => [15,23,39,71,135,27,43,75,139,51,83,147,99,163,195,29,45,77,141,53,85,149,101,165,197,57,89,153,105,169,201,113,177,209,225,30,46,78,142,54,86,150,102,166,198,58,90,154,106,170,202,114,178,210,226,60,92,156,108,172,204,116,180,212,228,120,184,216,232,240]
  | 5 => [31,47,79,143,55,87,151,103,167,199,59,91,155,107,171,203,115,179,211,227,61,93,157,109,173,205,117,181,213,229,121,185,217,233,241,62,94,158,110,174,206,118,182,214,230,122,186,218,234,242,124,188,220,236,244,248]
  | 6 => [63,95,159,111,175,207,119,183,215,231,123,187,219,235,243,125,189,221,237,245,249,126,190,222,238,246,250,252]
  | 7 => [127,191,223,239,247,251,253,254]
  | 8 => [255]
  | _ => []

theorem cover (d : Fin 9) : RowCover 8 d.val (choices d.val) := by
  revert d
  decide +kernel

def profile0_node2_cert : CutBound 8 := { lost := (rows 0 0 48 48 0 0 0 0), upper := (rows 49 50 196 200 208 224 192 192), lower := (rows 49 50 4 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 255 0 255 255 255), good := (rows 237 238 236 236 236 236 236 236) },{ target := 5, region := (rows 1 2 255 255 255 0 255 255), good := (rows 221 222 220 220 220 220 220 220) }] }

theorem profile0_node2 : Upper (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,48] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,48] 4 profile0_node2_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,48] 4 profile0_node2_cert).mp (by decide +kernel))

def profile0_node4_cert : CutBound 8 := { lost := (rows 0 32 16 48 0 0 0 0), upper := (rows 49 82 100 136 144 160 192 128), lower := (rows 49 82 100 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 255 0 255 255 255), good := (rows 237 238 236 236 236 236 236 236) },{ target := 5, region := (rows 1 255 4 255 255 0 255 255), good := (rows 219 218 222 218 218 218 218 218) }] }

theorem profile0_node4 : Upper (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,80,96] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,80,96] 4 profile0_node4_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,80,96] 4 profile0_node4_cert).mp (by decide +kernel))

def profile0_node5_cert : CutBound 8 := { lost := (rows 0 32 16 48 0 0 0 0), upper := (rows 49 82 164 200 208 224 192 192), lower := (rows 49 82 164 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 255 0 255 255 255), good := (rows 237 238 236 236 236 236 236 236) },{ target := 5, region := (rows 1 255 4 255 255 0 255 255), good := (rows 219 218 222 218 218 218 218 218) }] }

theorem profile0_node5 : Upper (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,80,160] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,80,160] 4 profile0_node5_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,80,160] 4 profile0_node5_cert).mp (by decide +kernel))

def profile0_node6_cert : CutBound 8 := { lost := (rows 64 0 16 80 0 0 0 0), upper := (rows 49 82 196 168 176 160 224 160), lower := (rows 49 82 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 2 255 255 0 255 255 255), good := (rows 237 238 236 236 236 236 236 236) },{ target := 6, region := (rows 255 2 4 255 255 255 0 255), good := (rows 185 187 189 185 185 185 185 185) }] }

theorem profile0_node6 : Upper (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,80,192] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,80,192] 4 profile0_node6_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,80,192] 4 profile0_node6_cert).mp (by decide +kernel))

def profile0_node3_route : Route 8 := (fun mask => (mask,id))

theorem profile0_node3 : Upper (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,80] 4 := by
  apply routed_branch (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,80] 4 (by decide) (choices 2) [96,160,192] profile0_node3_route
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,80] (choices 2) [96,160,192] profile0_node3_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node4
  · exact profile0_node5
  · exact profile0_node6

def profile0_node8_cert : CutBound 8 := { lost := (rows 0 48 0 48 0 0 0 0), upper := (rows 49 194 52 200 208 224 192 192), lower := (rows 49 194 52 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 255 0 255 255 255), good := (rows 235 234 238 234 234 234 234 234) },{ target := 5, region := (rows 1 255 4 255 255 0 255 255), good := (rows 219 218 222 218 218 218 218 218) }] }

theorem profile0_node8 : Upper (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,192,48] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,192,48] 4 profile0_node8_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,192,48] 4 profile0_node8_cert).mp (by decide +kernel))

def profile0_node9_cert : CutBound 8 := { lost := (rows 64 16 0 80 0 0 0 0), upper := (rows 49 194 84 168 176 160 224 160), lower := (rows 49 194 84 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 255 4 255 0 255 255 255), good := (rows 235 234 238 234 234 234 234 234) },{ target := 6, region := (rows 255 2 4 255 255 255 0 255), good := (rows 185 187 189 185 185 185 185 185) }] }

theorem profile0_node9 : Upper (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,192,80] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,192,80] 4 profile0_node9_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,192,80] 4 profile0_node9_cert).mp (by decide +kernel))

def profile0_node10_cert : CutBound 8 := { lost := (rows 0 48 48 0 0 0 0 0), upper := (rows 49 194 196 56 48 48 112 176), lower := (rows 49 194 196 8 16 32 64 128), losses := [{ target := 4, region := (rows 1 6 6 8 0 32 64 128), good := (rows 33 198 198 8 0 32 64 128) },{ target := 5, region := (rows 1 6 6 8 16 0 64 128), good := (rows 17 198 198 8 16 0 64 128) }] }

theorem profile0_node10 : Upper (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,192,192] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,192,192] 4 profile0_node10_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,192,192] 4 profile0_node10_cert).mp (by decide +kernel))

def profile0_node7_route : Route 8 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile0_node7 : Upper (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,192] 4 := by
  apply routed_branch (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,192] 4 (by decide) (choices 2) [48,80,192] profile0_node7_route
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48,192] (choices 2) [48,80,192] profile0_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node8
  · exact profile0_node9
  · exact profile0_node10

def profile0_node1_route : Route 8 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile0_node1 : Upper (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48] 4 := by
  apply routed_branch (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48] 4 (by decide) (choices 2) [48,80,192] profile0_node1_route
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [48] (choices 2) [48,80,192] profile0_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile0_node2
  · exact profile0_node3
  · exact profile0_node7

def profile0_node0_route : Route 8 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile0_node0 : Upper (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [] 4 := by
  apply routed_branch (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [] 4 (by decide) (choices 2) [48] profile0_node0_route
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [] (choices 2) [48] profile0_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile0_node1

theorem profile0 : Upper (D (n:=8) [32,32,32,32,2,2,2,2]) (R (n:=8) [32,32,32,32,2,2,2,2]) [] 4 := profile0_node0

def profile1_node3_cert : CutBound 8 := { lost := (rows 32 0 0 0 0 0 0 0), upper := (rows 25 98 100 136 144 160 192 128), lower := (rows 25 98 100 8 16 32 64 128), losses := [{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile1_node3 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [24,96,96] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [24,96,96] 4 profile1_node3_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [24,96,96] 4 profile1_node3_cert).mp (by decide +kernel))

def profile1_node4_cert : CutBound 8 := { lost := (rows 32 0 0 0 0 0 0 0), upper := (rows 25 98 164 200 208 224 192 192), lower := (rows 25 98 164 8 16 32 64 128), losses := [{ target := 5, region := (rows 255 2 4 255 255 0 255 255), good := (rows 217 219 221 217 217 217 217 217) }] }

theorem profile1_node4 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [24,96,160] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [24,96,160] 4 profile1_node4_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [24,96,160] 4 profile1_node4_cert).mp (by decide +kernel))

def profile1_node2_route : Route 8 := (fun mask => match mask with | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile1_node2 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [24,96] 4 := by
  apply routed_branch (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [24,96] 4 (by decide) (choices 2) [96,160] profile1_node2_route
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [24,96] (choices 2) [96,160] profile1_node2_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node3
  · exact profile1_node4

def profile1_node1_route : Route 8 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile1_node1 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [24] 4 := by
  apply routed_branch (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [24] 4 (by decide) (choices 2) [96] profile1_node1_route
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [24] (choices 2) [96] profile1_node1_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node2

def profile1_node6_cert : CutBound 8 := { lost := (rows 0 0 32 0 0 0 0 0), upper := (rows 41 50 196 200 208 224 192 192), lower := (rows 41 50 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 255 255 255 0 255 255), good := (rows 221 222 220 220 220 220 220 220) }] }

theorem profile1_node6 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,48] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,48] 4 profile1_node6_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,48] 4 profile1_node6_cert).mp (by decide +kernel))

def profile1_node8_cert : CutBound 8 := { lost := (rows 0 32 0 0 0 0 0 0), upper := (rows 41 82 100 136 144 160 192 128), lower := (rows 41 82 100 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 255 4 255 255 0 255 255), good := (rows 219 218 222 218 218 218 218 218) }] }

theorem profile1_node8 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,80,96] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,80,96] 4 profile1_node8_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,80,96] 4 profile1_node8_cert).mp (by decide +kernel))

def profile1_node9_cert : CutBound 8 := { lost := (rows 0 32 0 0 0 0 0 0), upper := (rows 41 82 164 200 208 224 192 192), lower := (rows 41 82 164 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 255 4 255 255 0 255 255), good := (rows 219 218 222 218 218 218 218 218) }] }

theorem profile1_node9 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,80,160] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,80,160] 4 profile1_node9_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,80,160] 4 profile1_node9_cert).mp (by decide +kernel))

def profile1_node10_cert : CutBound 8 := { lost := (rows 64 0 0 0 0 0 0 0), upper := (rows 41 82 196 168 176 160 224 160), lower := (rows 41 82 196 8 16 32 64 128), losses := [{ target := 6, region := (rows 255 2 4 255 255 255 0 255), good := (rows 185 187 189 185 185 185 185 185) }] }

theorem profile1_node10 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,80,192] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,80,192] 4 profile1_node10_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,80,192] 4 profile1_node10_cert).mp (by decide +kernel))

def profile1_node7_route : Route 8 := (fun mask => (mask,id))

theorem profile1_node7 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,80] 4 := by
  apply routed_branch (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,80] 4 (by decide) (choices 2) [96,160,192] profile1_node7_route
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,80] (choices 2) [96,160,192] profile1_node7_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node8
  · exact profile1_node9
  · exact profile1_node10

def profile1_node11_cert : CutBound 8 := { lost := (rows 0 0 32 0 0 0 0 0), upper := (rows 41 98 212 216 208 240 208 208), lower := (rows 41 98 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 255 255 255 0 255 255), good := (rows 221 222 220 220 220 220 220 220) }] }

theorem profile1_node11 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,96] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,96] 4 profile1_node11_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,96] 4 profile1_node11_cert).mp (by decide +kernel))

def profile1_node13_cert : CutBound 8 := { lost := (rows 0 32 0 0 0 0 0 0), upper := (rows 41 194 52 200 208 224 192 192), lower := (rows 41 194 52 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 255 4 255 255 0 255 255), good := (rows 219 218 222 218 218 218 218 218) }] }

theorem profile1_node13 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,192,48] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,192,48] 4 profile1_node13_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,192,48] 4 profile1_node13_cert).mp (by decide +kernel))

def profile1_node14_cert : CutBound 8 := { lost := (rows 64 0 0 0 0 0 0 0), upper := (rows 41 194 84 168 176 160 224 160), lower := (rows 41 194 84 8 16 32 64 128), losses := [{ target := 6, region := (rows 255 2 4 255 255 255 0 255), good := (rows 185 187 189 185 185 185 185 185) }] }

theorem profile1_node14 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,192,80] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,192,80] 4 profile1_node14_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,192,80] 4 profile1_node14_cert).mp (by decide +kernel))

def profile1_node15_cert : Bound 8 := { allowed := (rows 192 32 128 0 0 0 0 0), upper := (rows 41 194 100 152 144 176 208 144), lower := (rows 41 194 100 8 16 32 64 128), losses := [] }

theorem profile1_node15 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,192,96] 4 :=
  bound_sound (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,192,96] 4 profile1_node15_cert
    ((SmallBoolean.boundCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,192,96] 4 profile1_node15_cert).mp (by decide +kernel))

def profile1_node16_cert : Bound 8 := { allowed := (rows 192 32 32 0 0 0 0 0), upper := (rows 41 194 196 56 48 48 112 176), lower := (rows 41 194 196 8 16 32 64 128), losses := [] }

theorem profile1_node16 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,192,192] 4 :=
  bound_sound (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,192,192] 4 profile1_node16_cert
    ((SmallBoolean.boundCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,192,192] 4 profile1_node16_cert).mp (by decide +kernel))

def profile1_node12_route : Route 8 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile1_node12 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,192] 4 := by
  apply routed_branch (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,192] 4 (by decide) (choices 2) [48,80,96,192] profile1_node12_route
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40,192] (choices 2) [48,80,96,192] profile1_node12_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile1_node13
  · exact profile1_node14
  · exact profile1_node15
  · exact profile1_node16

def profile1_node5_route : Route 8 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile1_node5 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40] 4 := by
  apply routed_branch (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40] 4 (by decide) (choices 2) [48,80,96,192] profile1_node5_route
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [40] (choices 2) [48,80,96,192] profile1_node5_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile1_node6
  · exact profile1_node7
  · exact profile1_node11
  · exact profile1_node12

def profile1_node19_cert : CutBound 8 := { lost := (rows 0 32 0 0 0 0 0 0), upper := (rows 97 26 100 136 144 160 192 128), lower := (rows 97 26 100 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 255 4 255 255 0 255 255), good := (rows 219 218 222 218 218 218 218 218) }] }

theorem profile1_node19 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,24,96] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,24,96] 4 profile1_node19_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,24,96] 4 profile1_node19_cert).mp (by decide +kernel))

def profile1_node20_cert : CutBound 8 := { lost := (rows 0 32 0 0 0 0 0 0), upper := (rows 97 26 164 200 208 224 192 192), lower := (rows 97 26 164 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 255 4 255 255 0 255 255), good := (rows 219 218 222 218 218 218 218 218) }] }

theorem profile1_node20 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,24,160] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,24,160] 4 profile1_node20_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,24,160] 4 profile1_node20_cert).mp (by decide +kernel))

def profile1_node18_route : Route 8 := (fun mask => match mask with | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile1_node18 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,24] 4 := by
  apply routed_branch (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,24] 4 (by decide) (choices 2) [96,160] profile1_node18_route
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,24] (choices 2) [96,160] profile1_node18_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile1_node19
  · exact profile1_node20

def profile1_node21_cert : CutBound 8 := { lost := (rows 0 0 32 0 0 0 0 0), upper := (rows 97 42 212 216 208 240 208 208), lower := (rows 97 42 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 255 255 255 0 255 255), good := (rows 221 222 220 220 220 220 220 220) }] }

theorem profile1_node21 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,40] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,40] 4 profile1_node21_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,40] 4 profile1_node21_cert).mp (by decide +kernel))

def profile1_node22_cert : CutBound 8 := { lost := (rows 0 0 32 0 0 0 0 0), upper := (rows 97 98 156 152 152 184 216 152), lower := (rows 97 98 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 255 255 255 0 255 255), good := (rows 221 222 220 220 220 220 220 220) }] }

theorem profile1_node22 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,96] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,96] 4 profile1_node22_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,96] 4 profile1_node22_cert).mp (by decide +kernel))

def profile1_node24_cert : CutBound 8 := { lost := (rows 0 32 0 0 0 0 0 0), upper := (rows 97 138 52 200 208 224 192 192), lower := (rows 97 138 52 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 255 4 255 255 0 255 255), good := (rows 219 218 222 218 218 218 218 218) }] }

theorem profile1_node24 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,136,48] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,136,48] 4 profile1_node24_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,136,48] 4 profile1_node24_cert).mp (by decide +kernel))

def profile1_node25_cert : Bound 8 := { allowed := (rows 128 96 128 0 0 0 0 0), upper := (rows 97 138 100 152 144 176 208 144), lower := (rows 97 138 100 8 16 32 64 128), losses := [] }

theorem profile1_node25 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,136,96] 4 :=
  bound_sound (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,136,96] 4 profile1_node25_cert
    ((SmallBoolean.boundCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,136,96] 4 profile1_node25_cert).mp (by decide +kernel))

def profile1_node26_cert : CutBound 8 := { lost := (rows 128 0 0 0 0 0 0 0), upper := (rows 97 138 148 104 112 96 96 224), lower := (rows 97 138 148 8 16 32 64 128), losses := [{ target := 7, region := (rows 255 2 4 255 255 255 255 0), good := (rows 121 123 125 121 121 121 121 121) }] }

theorem profile1_node26 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,136,144] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,136,144] 4 profile1_node26_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,136,144] 4 profile1_node26_cert).mp (by decide +kernel))

def profile1_node27_cert : Bound 8 := { allowed := (rows 128 96 64 0 0 0 0 0), upper := (rows 97 138 164 88 80 112 80 208), lower := (rows 97 138 164 8 16 32 64 128), losses := [] }

theorem profile1_node27 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,136,160] 4 :=
  bound_sound (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,136,160] 4 profile1_node27_cert
    ((SmallBoolean.boundCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,136,160] 4 profile1_node27_cert).mp (by decide +kernel))

def profile1_node23_route : Route 8 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile1_node23 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,136] 4 := by
  apply routed_branch (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,136] 4 (by decide) (choices 2) [48,96,144,160] profile1_node23_route
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,136] (choices 2) [48,96,144,160] profile1_node23_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile1_node24
  · exact profile1_node25
  · exact profile1_node26
  · exact profile1_node27

def profile1_node28_cert : CutBound 8 := { lost := (rows 0 0 32 0 0 0 0 0), upper := (rows 97 162 220 216 216 248 216 216), lower := (rows 97 162 4 8 16 32 64 128), losses := [{ target := 5, region := (rows 1 2 255 255 255 0 255 255), good := (rows 221 222 220 220 220 220 220 220) }] }

theorem profile1_node28 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,160] 4 :=
  cut_bound_sound (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,160] 4 profile1_node28_cert
    ((SmallCut.boundCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96,160] 4 profile1_node28_cert).mp (by decide +kernel))

def profile1_node17_route : Route 8 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile1_node17 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96] 4 := by
  apply routed_branch (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96] 4 (by decide) (choices 2) [24,40,96,136,160] profile1_node17_route
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [96] (choices 2) [24,40,96,136,160] profile1_node17_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile1_node18
  · exact profile1_node21
  · exact profile1_node22
  · exact profile1_node23
  · exact profile1_node28

def profile1_node0_route : Route 8 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile1_node0 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [] 4 := by
  apply routed_branch (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [] 4 (by decide) (choices 2) [24,40,96] profile1_node0_route
    (by change RowCover 8 2 (choices 2); exact cover ⟨2,by decide⟩)
    ((SmallBoolean.routesCheck_true (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [] (choices 2) [24,40,96] profile1_node0_route).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile1_node1
  · exact profile1_node5
  · exact profile1_node17

theorem profile1 : Upper (D (n:=8) [32,32,32,17,17,2,2,2]) (R (n:=8) [32,32,32,17,17,2,2,2]) [] 4 := profile1_node0

def catalogue : List (List Nat) := [[2,2,2,2,32,32,32,32],[2,2,2,17,17,32,32,32]]

theorem catalogue_eq : hardProfiles 8 8 4 true=catalogue := by decide +kernel

theorem hard_upper (xs : List Nat) (member : xs∈hardProfiles 8 8 4 true) :
    Upper (n:=8) (D xs.reverse) (R xs.reverse) [] 4 := by
  rw [catalogue_eq] at member
  simp only [catalogue,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0
  · exact profile1
theorem profile_upper (xs : List Nat) (member : xs∈profiles 8 true 8 0 8 8) :
    Upper (n:=8) (D xs.reverse) (R xs.reverse) [] 4 :=
  upper_of_hard hard_upper xs member

theorem upper (E : Graph (Fin 8)) (loops : Loopless E) (budget : arcCount E=8)
    (degree : ∀x,2≤SparseSupport.outdegree E x+SparseSupport.indegree E x)
    (regularity : ∀x,(0<SparseSupport.outdegree E x ∧ 0<SparseSupport.indegree E x) ∨
      (true=true ∧ SparseSupport.outdegree E x+SparseSupport.indegree E x=2)) : score E≤4 := by
  have od (x) : SparseSupport.outdegree E x<8 := by
    have h := SparseDeletion.row_nonadjacent_bound E loops x
    omega
  have idg (x) : SparseSupport.indegree E x<8 := by
    have h := SparseDeletion.column_nonadjacent_bound E loops x
    omega
  have td : ((List.finRange 8).map (SparseSupport.outdegree E)).sum=8 := by
    have h := SparseSupport.arc_rows E
    exact h.symm.trans budget
  have te : ((List.finRange 8).map (SparseSupport.indegree E)).sum=8 := by
    have h := SparseSupport.arc_columns E
    exact h.symm.trans budget
  have member := sorted_member (SparseSupport.outdegree E) (SparseSupport.indegree E)
    true (by decide) od idg degree regularity td te
  obtain ⟨F,⟨iso⟩,prescribed⟩ := relabel_reversed E loops (fun x => by have := idg x; omega)
  have bound := profile_upper _ member F prescribed (by intro s h; simp at h)
  rw [GraphRelabeling.score_eq iso] at bound
  exact bound

#print axioms upper
end Delivery.SmallBudgetEightFinite8
