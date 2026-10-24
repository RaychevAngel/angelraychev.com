import SmallBudgetTenFinite7Profile034Part001

namespace Delivery.SmallBudgetTenFinite7
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile34_node178_column : Nat → Fin 7 := fun mask => match mask with | _ => 0

def profile34_node178_route : Route 7 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | _ => i)) | 72 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

theorem profile34_node178 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [48] 6 (by decide) (choices 2) [5,12,17,20,48,65,68,80] profile34_node178_route profile34_node178_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node179
  · exact profile34_node192
  · exact profile34_node211
  · exact profile34_node212
  · exact profile34_node232
  · exact profile34_node233
  · exact profile34_node234
  · exact profile34_node235

def profile34_node258_cert : CutBound 7 := { lost := (rows 48 0 0 0 0 0 0), upper := (rows 67 127 125 125 125 125 64), lower := (rows 67 2 4 8 16 32 64), losses := [{ target := 4, region := (rows 3 2 4 8 0 32 127), good := (rows 67 67 68 72 64 96 64) },{ target := 5, region := (rows 3 2 4 8 16 0 127), good := (rows 67 67 68 72 80 64 64) }] }

theorem profile34_node258 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [66] 6 125 profile34_node258_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [66] 6 125 profile34_node258_cert).mp (by decide +kernel))

def profile34_node262_cert : CutBound 7 := { lost := (rows 32 32 32 0 0 0 0), upper := (rows 81 7 14 56 112 96 64), lower := (rows 81 7 14 56 16 32 64), losses := [{ target := 5, region := (rows 25 14 12 8 16 0 127), good := (rows 81 71 79 95 81 64 64) }] }

theorem profile34_node262 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,10,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,10,48] 6 96 profile34_node262_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,10,48] 6 96 profile34_node262_cert).mp (by decide +kernel))

def profile34_node263_cert : CutBound 7 := { lost := (rows 32 32 32 32 0 0 0), upper := (rows 81 7 14 88 48 32 64), lower := (rows 81 7 14 88 16 32 64), losses := [{ target := 5, region := (rows 25 31 31 25 16 0 127), good := (rows 95 79 79 95 95 64 64) }] }

theorem profile34_node263 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,10,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,10,80] 6 32 profile34_node263_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,10,80] 6 32 profile34_node263_cert).mp (by decide +kernel))

def profile34_node264_cert : CutBound 7 := { lost := (rows 32 0 0 16 0 0 0), upper := (rows 81 7 14 104 48 48 64), lower := (rows 81 7 14 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 40 0 32 127), good := (rows 65 71 78 104 64 104 64) },{ target := 5, region := (rows 17 2 4 8 16 0 127), good := (rows 81 71 78 72 81 64 64) }] }

theorem profile34_node264 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,10,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,10,96] 6 48 profile34_node264_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,10,96] 6 48 profile34_node264_cert).mp (by decide +kernel))

def profile34_node261_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node261_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node261 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,10] 6 (by decide) (choices 2) [48,80,96] profile34_node261_route profile34_node261_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node262
  · exact profile34_node263
  · exact profile34_node264

def profile34_node265_cert : CutBound 7 := { lost := (rows 32 32 32 16 0 0 0), upper := (rows 81 7 22 104 120 104 64), lower := (rows 81 7 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 105 111 110 104 104 104 104) },{ target := 5, region := (rows 21 23 21 8 16 0 127), good := (rows 87 71 87 72 87 64 64) }] }

theorem profile34_node265 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,18] 6 104 profile34_node265_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,18] 6 104 profile34_node265_cert).mp (by decide +kernel))

def profile34_node266_cert : CutBound 7 := { lost := (rows 32 32 0 16 0 0 0), upper := (rows 81 7 28 106 114 98 64), lower := (rows 81 7 28 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 34 127), good := (rows 65 111 76 72 64 96 64) },{ target := 5, region := (rows 21 6 4 8 16 0 127), good := (rows 81 71 95 72 81 64 64) }] }

theorem profile34_node266 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,24] 6 98 profile34_node266_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,24] 6 98 profile34_node266_cert).mp (by decide +kernel))

def profile34_node268_cert : Bound 7 := { allowed := (rows 0 112 80 64 0 0 0), upper := (rows 81 7 38 56 88 104 64), lower := (rows 81 7 38 56 16 32 64), losses := [{ target := 5, region := (rows 25 2 4 8 24 0 127), good := (rows 81 71 70 89 81 64 64) }] }

theorem profile34_node268 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,34,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,34,48] 6 72 profile34_node268_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,34,48] 6 72 profile34_node268_cert).mp (by decide +kernel))

def profile34_node269_cert : CutBound 7 := { lost := (rows 32 0 0 32 0 0 0), upper := (rows 81 7 38 88 56 40 64), lower := (rows 81 7 38 88 16 32 64), losses := [{ target := 5, region := (rows 25 2 4 25 16 0 127), good := (rows 89 79 70 89 89 64 64) }] }

theorem profile34_node269 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,34,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,34,80] 6 40 profile34_node269_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,34,80] 6 40 profile34_node269_cert).mp (by decide +kernel))

def profile34_node270_cert : Bound 7 := { allowed := (rows 32 112 80 0 0 0 0), upper := (rows 81 7 38 104 24 56 64), lower := (rows 81 7 38 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 44 0 32 127), good := (rows 65 79 110 104 64 104 64) }] }

theorem profile34_node270 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,34,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,34,96] 6 24 profile34_node270_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,34,96] 6 24 profile34_node270_cert).mp (by decide +kernel))

def profile34_node267_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node267_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node267 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,34] 6 (by decide) (choices 2) [48,80,96] profile34_node267_route profile34_node267_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node268
  · exact profile34_node269
  · exact profile34_node270

def profile34_node272_cert : CutBound 7 := { lost := (rows 32 32 16 0 0 0 0), upper := (rows 81 7 44 26 112 96 64), lower := (rows 81 7 44 26 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 127 127), good := (rows 97 103 108 110 96 96 96) },{ target := 5, region := (rows 25 6 4 8 16 0 127), good := (rows 81 71 79 91 81 64 64) }] }

theorem profile34_node272 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,40,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,40,18] 6 96 profile34_node272_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,40,18] 6 96 profile34_node272_cert).mp (by decide +kernel))

def profile34_node273_cert : CutBound 7 := { lost := (rows 32 32 16 0 0 0 0), upper := (rows 81 7 44 42 80 112 64), lower := (rows 81 7 44 42 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 32 127), good := (rows 65 71 108 110 64 96 64) },{ target := 5, region := (rows 127 6 4 8 127 0 127), good := (rows 81 87 95 91 81 81 81) }] }

theorem profile34_node273 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,40,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,40,34] 6 80 profile34_node273_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,40,34] 6 80 profile34_node273_cert).mp (by decide +kernel))

def profile34_node274_cert : Bound 7 := { allowed := (rows 32 112 64 64 0 0 0), upper := (rows 81 7 44 56 82 98 64), lower := (rows 81 7 44 56 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 34 127), good := (rows 65 103 108 108 64 96 64) }] }

theorem profile34_node274 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,40,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,40,48] 6 66 profile34_node274_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,40,48] 6 66 profile34_node274_cert).mp (by decide +kernel))

def profile34_node275_cert : CutBound 7 := { lost := (rows 32 0 0 48 0 0 0), upper := (rows 81 7 44 74 48 48 64), lower := (rows 81 7 44 74 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 32 127), good := (rows 65 79 108 74 64 96 64) },{ target := 5, region := (rows 17 2 4 10 16 0 127), good := (rows 81 79 76 74 81 64 64) }] }

theorem profile34_node275 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,40,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,40,66] 6 48 profile34_node275_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,40,66] 6 48 profile34_node275_cert).mp (by decide +kernel))

def profile34_node276_cert : CutBound 7 := { lost := (rows 32 32 0 32 0 0 0), upper := (rows 81 7 44 88 50 34 64), lower := (rows 81 7 44 88 16 32 64), losses := [{ target := 5, region := (rows 25 6 4 25 16 0 127), good := (rows 89 79 79 89 89 64 64) }] }

theorem profile34_node276 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,40,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,40,80] 6 34 profile34_node276_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,40,80] 6 34 profile34_node276_cert).mp (by decide +kernel))

def profile34_node277_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 81 7 44 104 18 50 64), lower := (rows 81 7 44 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 44 44 0 32 127), good := (rows 65 79 108 108 64 108 64) }] }

theorem profile34_node277 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,40,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,40,96] 6 18 profile34_node277_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,40,96] 6 18 profile34_node277_cert).mp (by decide +kernel))

def profile34_node271_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node271_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node271 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,40] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,40] 6 (by decide) (choices 2) [18,34,48,66,80,96] profile34_node271_route profile34_node271_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node272
  · exact profile34_node273
  · exact profile34_node274
  · exact profile34_node275
  · exact profile34_node276
  · exact profile34_node277

def profile34_node278_cert : CutBound 7 := { lost := (rows 32 32 0 16 0 0 0), upper := (rows 81 7 52 106 122 106 64), lower := (rows 81 7 52 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 34 127), good := (rows 65 111 100 72 64 96 64) },{ target := 5, region := (rows 21 6 4 8 16 0 127), good := (rows 81 71 87 72 81 64 64) }] }

theorem profile34_node278 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,48] 6 106 profile34_node278_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,48] 6 106 profile34_node278_cert).mp (by decide +kernel))

def profile34_node279_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 81 7 70 56 56 56 64), lower := (rows 81 7 70 8 16 32 64), losses := [{ target := 4, region := (rows 1 3 7 8 0 32 127), good := (rows 71 71 70 72 64 96 64) }] }

theorem profile34_node279 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,66] 6 56 profile34_node279_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,66] 6 56 profile34_node279_cert).mp (by decide +kernel))

def profile34_node280_cert : CutBound 7 := { lost := (rows 32 0 48 0 0 0 0), upper := (rows 81 7 76 58 50 50 64), lower := (rows 81 7 76 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 32 127), good := (rows 65 71 76 76 64 96 64) },{ target := 5, region := (rows 17 2 12 8 16 0 127), good := (rows 81 71 76 76 81 64 64) }] }

theorem profile34_node280 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,72] 6 50 profile34_node280_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,72] 6 50 profile34_node280_cert).mp (by decide +kernel))

def profile34_node281_cert : CutBound 7 := { lost := (rows 32 32 32 16 0 0 0), upper := (rows 81 7 84 42 58 42 64), lower := (rows 81 7 84 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 34 127), good := (rows 65 111 68 72 64 96 64) },{ target := 5, region := (rows 21 23 21 8 16 0 127), good := (rows 87 71 87 72 87 64 64) }] }

theorem profile34_node281 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,80] 6 42 profile34_node281_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,80] 6 42 profile34_node281_cert).mp (by decide +kernel))

def profile34_node282_cert : CutBound 7 := { lost := (rows 32 0 16 0 0 0 0), upper := (rows 81 7 100 58 58 58 64), lower := (rows 81 7 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 36 8 0 32 127), good := (rows 65 71 100 72 64 100 64) },{ target := 5, region := (rows 17 2 4 8 16 0 127), good := (rows 81 71 68 72 81 64 64) }] }

theorem profile34_node282 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,96] 6 58 profile34_node282_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5,96] 6 58 profile34_node282_cert).mp (by decide +kernel))

def profile34_node260_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | _ => 0

def profile34_node260_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node260 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,5] 6 (by decide) (choices 2) [10,18,24,34,40,48,66,72,80,96] profile34_node260_route profile34_node260_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node261
  · exact profile34_node265
  · exact profile34_node266
  · exact profile34_node267
  · exact profile34_node271
  · exact profile34_node278
  · exact profile34_node279
  · exact profile34_node280
  · exact profile34_node281
  · exact profile34_node282

def profile34_node285_cert : CutBound 7 := { lost := (rows 32 32 32 0 0 0 0), upper := (rows 81 14 7 56 112 96 64), lower := (rows 81 14 7 56 16 32 64), losses := [{ target := 5, region := (rows 25 10 14 8 16 0 127), good := (rows 81 79 71 95 81 64 64) }] }

theorem profile34_node285 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,3,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,3,48] 6 96 profile34_node285_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,3,48] 6 96 profile34_node285_cert).mp (by decide +kernel))

def profile34_node286_cert : CutBound 7 := { lost := (rows 32 32 32 32 0 0 0), upper := (rows 81 14 7 88 48 32 64), lower := (rows 81 14 7 88 16 32 64), losses := [{ target := 5, region := (rows 25 31 31 25 16 0 127), good := (rows 95 79 79 95 95 64 64) }] }

theorem profile34_node286 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,3,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,3,80] 6 32 profile34_node286_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,3,80] 6 32 profile34_node286_cert).mp (by decide +kernel))

def profile34_node287_cert : CutBound 7 := { lost := (rows 32 0 0 16 0 0 0), upper := (rows 81 14 7 104 48 48 64), lower := (rows 81 14 7 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 40 0 32 127), good := (rows 65 78 71 104 64 104 64) },{ target := 5, region := (rows 17 2 4 8 16 0 127), good := (rows 81 78 71 72 81 64 64) }] }

theorem profile34_node287 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,3,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,3,96] 6 48 profile34_node287_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,3,96] 6 48 profile34_node287_cert).mp (by decide +kernel))

def profile34_node284_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node284_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node284 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,3] 6 (by decide) (choices 2) [48,80,96] profile34_node284_route profile34_node284_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node285
  · exact profile34_node286
  · exact profile34_node287

def profile34_node288_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 81 14 21 106 114 98 64), lower := (rows 81 14 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 14 0 38 127), good := (rows 65 110 111 72 64 96 64) }] }

theorem profile34_node288 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,17] 6 98 profile34_node288_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,17] 6 98 profile34_node288_cert).mp (by decide +kernel))

def profile34_node289_cert : CutBound 7 := { lost := (rows 32 0 0 16 0 0 0), upper := (rows 81 14 22 105 113 97 64), lower := (rows 81 14 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 105 78 70 72 64 96 64) },{ target := 5, region := (rows 21 2 4 8 16 0 127), good := (rows 81 79 87 72 81 64 64) }] }

theorem profile34_node289 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,18] 6 97 profile34_node289_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,18] 6 97 profile34_node289_cert).mp (by decide +kernel))

def profile34_node291_cert : CutBound 7 := { lost := (rows 32 0 16 0 0 0 0), upper := (rows 81 14 37 26 112 96 64), lower := (rows 81 14 37 26 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 127 127), good := (rows 101 110 101 106 96 96 96) },{ target := 5, region := (rows 25 2 4 8 16 0 127), good := (rows 81 79 69 91 81 64 64) }] }

theorem profile34_node291 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,33,18] 6 96 profile34_node291_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,33,18] 6 96 profile34_node291_cert).mp (by decide +kernel))

def profile34_node292_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 81 14 37 42 80 112 64), lower := (rows 81 14 37 42 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 12 0 32 127), good := (rows 65 78 111 106 64 96 64) }] }

theorem profile34_node292 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,33,34] 6 80 profile34_node292_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,33,34] 6 80 profile34_node292_cert).mp (by decide +kernel))

def profile34_node293_cert : Bound 7 := { allowed := (rows 0 112 80 64 0 0 0), upper := (rows 81 14 37 56 82 98 64), lower := (rows 81 14 37 56 16 32 64), losses := [{ target := 5, region := (rows 27 2 4 8 18 0 127), good := (rows 81 95 69 89 81 64 64) }] }

theorem profile34_node293 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,33,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,33,48] 6 66 profile34_node293_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,33,48] 6 66 profile34_node293_cert).mp (by decide +kernel))

def profile34_node294_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 81 14 37 74 48 48 64), lower := (rows 81 14 37 74 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 14 0 32 127), good := (rows 65 78 111 74 64 96 64) }] }

theorem profile34_node294 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,33,66] 6 48 profile34_node294_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,33,66] 6 48 profile34_node294_cert).mp (by decide +kernel))

def profile34_node295_cert : CutBound 7 := { lost := (rows 32 32 0 32 0 0 0), upper := (rows 81 14 37 88 50 34 64), lower := (rows 81 14 37 88 16 32 64), losses := [{ target := 5, region := (rows 25 6 4 25 16 0 127), good := (rows 89 79 79 89 89 64 64) }] }

theorem profile34_node295 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,33,80] 6 34 profile34_node295_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,33,80] 6 34 profile34_node295_cert).mp (by decide +kernel))

def profile34_node296_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 81 14 37 104 18 50 64), lower := (rows 81 14 37 104 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 44 0 32 127), good := (rows 65 78 111 104 64 104 64) }] }

theorem profile34_node296 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,33,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,33,96] 6 18 profile34_node296_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,33,96] 6 18 profile34_node296_cert).mp (by decide +kernel))

def profile34_node290_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node290_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node290 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,33] 6 (by decide) (choices 2) [18,34,48,66,80,96] profile34_node290_route profile34_node290_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node291
  · exact profile34_node292
  · exact profile34_node293
  · exact profile34_node294
  · exact profile34_node295
  · exact profile34_node296

def profile34_node298_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 81 14 38 25 112 96 64), lower := (rows 81 14 38 25 16 32 64), losses := [{ target := 4, region := (rows 1 10 14 8 0 127 127), good := (rows 97 110 102 111 96 96 96) }] }

theorem profile34_node298 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,34,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,34,17] 6 96 profile34_node298_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,34,17] 6 96 profile34_node298_cert).mp (by decide +kernel))

def profile34_node299_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 81 14 38 41 80 112 64), lower := (rows 81 14 38 41 16 32 64), losses := [{ target := 4, region := (rows 1 10 12 8 0 32 127), good := (rows 65 78 102 111 64 96 64) }] }

theorem profile34_node299 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,34,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,34,33] 6 80 profile34_node299_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,34,33] 6 80 profile34_node299_cert).mp (by decide +kernel))

def profile34_node300_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 81 14 38 56 81 97 64), lower := (rows 81 14 38 56 16 32 64), losses := [{ target := 4, region := (rows 1 10 12 8 0 33 127), good := (rows 97 78 102 110 64 96 64) }] }

theorem profile34_node300 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,34,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,34,48] 6 65 profile34_node300_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,34,48] 6 65 profile34_node300_cert).mp (by decide +kernel))

def profile34_node301_cert : CutBound 7 := { lost := (rows 32 0 0 48 0 0 0), upper := (rows 81 14 38 73 48 48 64), lower := (rows 81 14 38 73 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 32 127), good := (rows 73 78 102 73 64 96 64) },{ target := 5, region := (rows 17 2 4 25 16 0 127), good := (rows 89 78 70 73 89 64 64) }] }

theorem profile34_node301 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,34,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,34,65] 6 48 profile34_node301_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,34,65] 6 48 profile34_node301_cert).mp (by decide +kernel))

def profile34_node302_cert : CutBound 7 := { lost := (rows 32 0 0 32 0 0 0), upper := (rows 81 14 38 88 49 33 64), lower := (rows 81 14 38 88 16 32 64), losses := [{ target := 5, region := (rows 25 2 4 25 16 0 127), good := (rows 89 79 70 89 89 64 64) }] }

theorem profile34_node302 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,34,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,34,80] 6 33 profile34_node302_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,34,80] 6 33 profile34_node302_cert).mp (by decide +kernel))

def profile34_node303_cert : CutBound 7 := { lost := (rows 0 16 16 16 0 0 0), upper := (rows 81 14 38 104 17 49 64), lower := (rows 81 14 38 104 16 32 64), losses := [{ target := 4, region := (rows 1 46 44 44 0 32 127), good := (rows 65 78 110 110 64 110 64) }] }

theorem profile34_node303 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,34,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,34,96] 6 17 profile34_node303_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,34,96] 6 17 profile34_node303_cert).mp (by decide +kernel))

def profile34_node297_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node297_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node297 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,34] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,34] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile34_node297_route profile34_node297_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node298
  · exact profile34_node299
  · exact profile34_node300
  · exact profile34_node301
  · exact profile34_node302
  · exact profile34_node303

def profile34_node305_cert : CutBound 7 := { lost := (rows 32 32 0 32 0 0 0), upper := (rows 81 14 52 11 112 96 64), lower := (rows 81 14 52 11 16 32 64), losses := [{ target := 5, region := (rows 21 6 4 14 16 0 127), good := (rows 81 79 95 75 81 64 64) }] }

theorem profile34_node305 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,48,3] 6 96 profile34_node305_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,48,3] 6 96 profile34_node305_cert).mp (by decide +kernel))

def profile34_node306_cert : Bound 7 := { allowed := (rows 0 112 64 80 0 0 0), upper := (rows 81 14 52 41 82 98 64), lower := (rows 81 14 52 41 16 32 64), losses := [{ target := 5, region := (rows 23 2 4 8 18 0 127), good := (rows 81 95 85 73 81 64 64) }] }

theorem profile34_node306 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,48,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,48,33] 6 66 profile34_node306_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,48,33] 6 66 profile34_node306_cert).mp (by decide +kernel))

def profile34_node307_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 81 14 52 42 81 97 64), lower := (rows 81 14 52 42 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 12 0 33 127), good := (rows 97 78 110 106 64 96 64) }] }

theorem profile34_node307 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,48,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,48,34] 6 65 profile34_node307_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,48,34] 6 65 profile34_node307_cert).mp (by decide +kernel))

def profile34_node308_cert : Bound 7 := { allowed := (rows 32 112 64 32 0 0 0), upper := (rows 81 14 52 73 50 34 64), lower := (rows 81 14 52 73 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 34 127), good := (rows 73 110 100 73 64 96 64) }] }

theorem profile34_node308 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,48,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,48,65] 6 34 profile34_node308_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,48,65] 6 34 profile34_node308_cert).mp (by decide +kernel))

def profile34_node309_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 81 14 52 74 49 33 64), lower := (rows 81 14 52 74 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 14 0 33 127), good := (rows 97 78 110 74 64 96 64) }] }

theorem profile34_node309 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,48,66] 6 33 profile34_node309_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,48,66] 6 33 profile34_node309_cert).mp (by decide +kernel))

def profile34_node310_cert : Bound 7 := { allowed := (rows 32 112 64 16 0 0 0), upper := (rows 81 14 52 104 19 35 64), lower := (rows 81 14 52 104 16 32 64), losses := [] }

theorem profile34_node310 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,48,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,48,96] 6 3 profile34_node310_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,48,96] 6 3 profile34_node310_cert).mp (by decide +kernel))

def profile34_node304_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node304_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node304 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,48] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,48] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile34_node304_route profile34_node304_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node305
  · exact profile34_node306
  · exact profile34_node307
  · exact profile34_node308
  · exact profile34_node309
  · exact profile34_node310

def profile34_node311_cert : CutBound 7 := { lost := (rows 32 0 48 0 0 0 0), upper := (rows 81 14 69 58 50 50 64), lower := (rows 81 14 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 8 0 32 127), good := (rows 69 78 69 72 64 96 64) },{ target := 5, region := (rows 17 2 21 8 16 0 127), good := (rows 85 78 69 72 85 64 64) }] }

theorem profile34_node311 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,65] 6 50 profile34_node311_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,65] 6 50 profile34_node311_cert).mp (by decide +kernel))

def profile34_node312_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 81 14 70 57 49 49 64), lower := (rows 81 14 70 8 16 32 64), losses := [{ target := 4, region := (rows 1 10 14 8 0 32 127), good := (rows 65 78 70 78 64 96 64) }] }

theorem profile34_node312 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,66] 6 49 profile34_node312_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,66] 6 49 profile34_node312_cert).mp (by decide +kernel))

def profile34_node313_cert : CutBound 7 := { lost := (rows 32 0 32 0 0 0 0), upper := (rows 81 14 84 43 51 35 64), lower := (rows 81 14 84 8 16 32 64), losses := [{ target := 5, region := (rows 21 2 21 8 16 0 127), good := (rows 85 79 85 72 85 64 64) }] }

theorem profile34_node313 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,80] 6 35 profile34_node313_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,80] 6 35 profile34_node313_cert).mp (by decide +kernel))

def profile34_node314_cert : CutBound 7 := { lost := (rows 32 0 16 0 0 0 0), upper := (rows 81 14 100 59 51 51 64), lower := (rows 81 14 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 36 8 0 32 127), good := (rows 65 78 100 72 64 100 64) },{ target := 5, region := (rows 17 2 4 8 16 0 127), good := (rows 81 78 68 72 81 64 64) }] }

theorem profile34_node314 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,96] 6 51 profile34_node314_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12,96] 6 51 profile34_node314_cert).mp (by decide +kernel))

def profile34_node283_column : Nat → Fin 7 := fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | _ => 0

def profile34_node283_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node283 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,12] 6 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96] profile34_node283_route profile34_node283_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node284
  · exact profile34_node288
  · exact profile34_node289
  · exact profile34_node290
  · exact profile34_node297
  · exact profile34_node304
  · exact profile34_node311
  · exact profile34_node312
  · exact profile34_node313
  · exact profile34_node314

def profile34_node315_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 81 19 110 110 126 110 64), lower := (rows 81 19 4 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 34 127), good := (rows 65 111 68 72 64 96 64) }] }

theorem profile34_node315 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,17] 6 110 profile34_node315_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,17] 6 110 profile34_node315_cert).mp (by decide +kernel))

def profile34_node317_cert : CutBound 7 := { lost := (rows 32 32 32 16 0 0 0), upper := (rows 81 22 7 104 120 104 64), lower := (rows 81 22 7 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 127 0 127 127), good := (rows 105 110 111 104 104 104 104) },{ target := 5, region := (rows 19 19 23 8 16 0 127), good := (rows 87 87 71 72 87 64 64) }] }

theorem profile34_node317 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,3] 6 104 profile34_node317_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,3] 6 104 profile34_node317_cert).mp (by decide +kernel))

def profile34_node318_cert : CutBound 7 := { lost := (rows 32 0 0 16 0 0 0), upper := (rows 81 22 13 106 114 98 64), lower := (rows 81 22 13 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 34 127), good := (rows 65 110 77 72 64 96 64) },{ target := 5, region := (rows 19 2 4 8 16 0 127), good := (rows 81 87 77 72 81 64 64) }] }

theorem profile34_node318 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,9] 6 98 profile34_node318_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,9] 6 98 profile34_node318_cert).mp (by decide +kernel))

def profile34_node319_cert : CutBound 7 := { lost := (rows 32 0 0 16 0 0 0), upper := (rows 81 22 14 105 113 97 64), lower := (rows 81 22 14 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 105 70 78 72 64 96 64) },{ target := 5, region := (rows 19 2 4 8 16 0 127), good := (rows 81 87 79 72 81 64 64) }] }

theorem profile34_node319 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,10] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,10] 6 97 profile34_node319_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,10] 6 97 profile34_node319_cert).mp (by decide +kernel))

def profile34_node320_cert : CutBound 7 := { lost := (rows 32 0 0 16 0 0 0), upper := (rows 81 22 37 106 122 106 64), lower := (rows 81 22 37 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 34 127), good := (rows 65 110 101 72 64 96 64) },{ target := 5, region := (rows 19 2 4 8 16 0 127), good := (rows 81 87 69 72 81 64 64) }] }

theorem profile34_node320 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,33] 6 106 profile34_node320_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,33] 6 106 profile34_node320_cert).mp (by decide +kernel))

def profile34_node321_cert : CutBound 7 := { lost := (rows 32 0 0 16 0 0 0), upper := (rows 81 22 38 105 121 105 64), lower := (rows 81 22 38 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 105 70 102 72 64 96 64) },{ target := 5, region := (rows 19 2 4 8 16 0 127), good := (rows 81 87 71 72 81 64 64) }] }

theorem profile34_node321 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,34] 6 105 profile34_node321_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,34] 6 105 profile34_node321_cert).mp (by decide +kernel))

def profile34_node323_cert : CutBound 7 := { lost := (rows 32 0 16 32 0 0 0), upper := (rows 81 22 44 11 112 96 64), lower := (rows 81 22 44 11 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 127 127), good := (rows 97 102 108 111 96 96 96) },{ target := 5, region := (rows 19 2 4 10 16 0 127), good := (rows 81 95 76 75 81 64 64) }] }

theorem profile34_node323 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,40,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,40,3] 6 96 profile34_node323_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,40,3] 6 96 profile34_node323_cert).mp (by decide +kernel))

def profile34_node324_cert : Bound 7 := { allowed := (rows 32 96 64 80 0 0 0), upper := (rows 81 22 44 41 82 98 64), lower := (rows 81 22 44 41 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 34 127), good := (rows 65 102 108 109 64 96 64) }] }

theorem profile34_node324 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,40,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,40,33] 6 66 profile34_node324_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,40,33] 6 66 profile34_node324_cert).mp (by decide +kernel))

def profile34_node325_cert : Bound 7 := { allowed := (rows 32 96 64 80 0 0 0), upper := (rows 81 22 44 42 81 97 64), lower := (rows 81 22 44 42 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 33 127), good := (rows 97 70 108 110 64 96 64) }] }

theorem profile34_node325 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,40,34] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,40,34] 6 65 profile34_node325_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,40,34] 6 65 profile34_node325_cert).mp (by decide +kernel))

def profile34_node326_cert : Bound 7 := { allowed := (rows 32 96 80 32 0 0 0), upper := (rows 81 22 44 73 50 34 64), lower := (rows 81 22 44 73 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 34 127), good := (rows 73 102 108 73 64 96 64) }] }

theorem profile34_node326 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,40,65] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,40,65] 6 34 profile34_node326_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,40,65] 6 34 profile34_node326_cert).mp (by decide +kernel))

def profile34_node327_cert : Bound 7 := { allowed := (rows 32 96 80 32 0 0 0), upper := (rows 81 22 44 74 49 33 64), lower := (rows 81 22 44 74 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 33 127), good := (rows 97 78 108 74 64 96 64) }] }

theorem profile34_node327 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,40,66] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,40,66] 6 33 profile34_node327_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,40,66] 6 33 profile34_node327_cert).mp (by decide +kernel))

def profile34_node328_cert : Bound 7 := { allowed := (rows 32 96 80 16 0 0 0), upper := (rows 81 22 44 104 19 35 64), lower := (rows 81 22 44 104 16 32 64), losses := [] }

theorem profile34_node328 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,40,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,40,96] 6 3 profile34_node328_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,40,96] 6 3 profile34_node328_cert).mp (by decide +kernel))

def profile34_node322_column : Nat → Fin 7 := fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node322_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node322 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,40] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,40] 6 (by decide) (choices 2) [3,33,34,65,66,96] profile34_node322_route profile34_node322_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node323
  · exact profile34_node324
  · exact profile34_node325
  · exact profile34_node326
  · exact profile34_node327
  · exact profile34_node328

def profile34_node329_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 81 22 69 42 58 42 64), lower := (rows 81 22 69 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 5 10 0 34 127), good := (rows 69 110 69 72 64 96 64) }] }

theorem profile34_node329 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,65] 6 42 profile34_node329_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,65] 6 42 profile34_node329_cert).mp (by decide +kernel))

def profile34_node330_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 81 22 70 41 57 41 64), lower := (rows 81 22 70 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 9 0 33 127), good := (rows 105 70 70 72 64 96 64) }] }

theorem profile34_node330 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,66] 6 41 profile34_node330_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,66] 6 41 profile34_node330_cert).mp (by decide +kernel))

def profile34_node331_cert : CutBound 7 := { lost := (rows 32 0 48 0 0 0 0), upper := (rows 81 22 76 43 51 35 64), lower := (rows 81 22 76 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 32 127), good := (rows 65 70 76 76 64 96 64) },{ target := 5, region := (rows 19 2 12 8 16 0 127), good := (rows 81 87 76 76 81 64 64) }] }

theorem profile34_node331 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,72] 6 35 profile34_node331_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,72] 6 35 profile34_node331_cert).mp (by decide +kernel))

def profile34_node332_cert : Bound 7 := { allowed := (rows 32 96 0 112 0 0 0), upper := (rows 81 22 100 43 59 43 64), lower := (rows 81 22 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 36 8 0 32 127), good := (rows 65 70 100 72 64 100 64) }] }

theorem profile34_node332 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,96] 6 43 profile34_node332_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20,96] 6 43 profile34_node332_cert).mp (by decide +kernel))

def profile34_node316_column : Nat → Fin 7 := fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node316_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node316 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,20] 6 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] profile34_node316_route profile34_node316_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node317
  · exact profile34_node318
  · exact profile34_node319
  · exact profile34_node320
  · exact profile34_node321
  · exact profile34_node322
  · exact profile34_node329
  · exact profile34_node330
  · exact profile34_node331
  · exact profile34_node332

def profile34_node335_cert : CutBound 7 := { lost := (rows 32 16 0 0 0 0 0), upper := (rows 81 35 14 28 112 96 64), lower := (rows 81 35 14 28 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 99 99 110 108 96 96 96) },{ target := 5, region := (rows 25 2 4 8 16 0 127), good := (rows 81 67 79 93 81 64 64) }] }

theorem profile34_node335 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,10,20] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,10,20] 6 96 profile34_node335_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,10,20] 6 96 profile34_node335_cert).mp (by decide +kernel))

def profile34_node336_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 81 35 14 44 80 112 64), lower := (rows 81 35 14 44 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 32 127), good := (rows 65 111 78 108 64 96 64) }] }

theorem profile34_node336 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,10,36] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,10,36] 6 80 profile34_node336_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,10,36] 6 80 profile34_node336_cert).mp (by decide +kernel))

def profile34_node337_cert : Bound 7 := { allowed := (rows 0 80 112 64 0 0 0), upper := (rows 81 35 14 56 84 100 64), lower := (rows 81 35 14 56 16 32 64), losses := [{ target := 5, region := (rows 29 2 4 8 20 0 127), good := (rows 81 67 95 89 81 64 64) }] }

theorem profile34_node337 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,10,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,10,48] 6 68 profile34_node337_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,10,48] 6 68 profile34_node337_cert).mp (by decide +kernel))

def profile34_node338_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 81 35 14 76 48 48 64), lower := (rows 81 35 14 76 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 14 0 32 127), good := (rows 65 111 78 76 64 96 64) }] }

theorem profile34_node338 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,10,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,10,68] 6 48 profile34_node338_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,10,68] 6 48 profile34_node338_cert).mp (by decide +kernel))

def profile34_node339_cert : CutBound 7 := { lost := (rows 32 0 32 32 0 0 0), upper := (rows 81 35 14 88 52 36 64), lower := (rows 81 35 14 88 16 32 64), losses := [{ target := 5, region := (rows 25 2 6 25 16 0 127), good := (rows 89 79 79 89 89 64 64) }] }

theorem profile34_node339 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,10,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,10,80] 6 36 profile34_node339_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,10,80] 6 36 profile34_node339_cert).mp (by decide +kernel))

def profile34_node340_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 81 35 14 104 20 52 64), lower := (rows 81 35 14 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 42 0 32 127), good := (rows 65 111 78 104 64 104 64) }] }

theorem profile34_node340 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,10,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,10,96] 6 20 profile34_node340_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,10,96] 6 20 profile34_node340_cert).mp (by decide +kernel))

def profile34_node334_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | _ => 0

def profile34_node334_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node334 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,10] 6 (by decide) (choices 2) [20,36,48,68,80,96] profile34_node334_route profile34_node334_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node335
  · exact profile34_node336
  · exact profile34_node337
  · exact profile34_node338
  · exact profile34_node339
  · exact profile34_node340

def profile34_node341_cert : CutBound 7 := { lost := (rows 32 0 0 16 0 0 0), upper := (rows 81 35 22 108 124 108 64), lower := (rows 81 35 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 12 0 36 127), good := (rows 65 99 110 72 64 96 64) },{ target := 5, region := (rows 21 2 4 8 16 0 127), good := (rows 81 67 87 72 81 64 64) }] }

theorem profile34_node341 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,18] 6 108 profile34_node341_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,18] 6 108 profile34_node341_cert).mp (by decide +kernel))

def profile34_node343_cert : CutBound 7 := { lost := (rows 32 16 0 0 0 0 0), upper := (rows 81 35 28 14 112 96 64), lower := (rows 81 35 28 14 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 127 127), good := (rows 99 99 108 110 96 96 96) },{ target := 5, region := (rows 21 2 4 8 16 0 127), good := (rows 81 67 93 79 81 64 64) }] }

theorem profile34_node343 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,24,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,24,6] 6 96 profile34_node343_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,24,6] 6 96 profile34_node343_cert).mp (by decide +kernel))

def profile34_node344_cert : Bound 7 := { allowed := (rows 32 80 96 64 0 0 0), upper := (rows 81 35 28 42 84 100 64), lower := (rows 81 35 28 42 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 36 127), good := (rows 65 107 108 106 64 96 64) }] }

theorem profile34_node344 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,24,34] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,24,34] 6 68 profile34_node344_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,24,34] 6 68 profile34_node344_cert).mp (by decide +kernel))

def profile34_node345_cert : Bound 7 := { allowed := (rows 32 64 96 80 0 0 0), upper := (rows 81 35 28 44 82 98 64), lower := (rows 81 35 28 44 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 35 127), good := (rows 99 99 76 108 64 96 64) }] }

theorem profile34_node345 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,24,36] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,24,36] 6 66 profile34_node345_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,24,36] 6 66 profile34_node345_cert).mp (by decide +kernel))

def profile34_node346_cert : Bound 7 := { allowed := (rows 32 80 96 32 0 0 0), upper := (rows 81 35 28 74 52 36 64), lower := (rows 81 35 28 74 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 36 127), good := (rows 65 107 108 74 64 96 64) }] }

theorem profile34_node346 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,24,66] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,24,66] 6 36 profile34_node346_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,24,66] 6 36 profile34_node346_cert).mp (by decide +kernel))

def profile34_node347_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 81 35 28 76 50 34 64), lower := (rows 81 35 28 76 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 12 0 35 127), good := (rows 99 99 76 76 64 96 64) }] }

theorem profile34_node347 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,24,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,24,68] 6 34 profile34_node347_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,24,68] 6 34 profile34_node347_cert).mp (by decide +kernel))

def profile34_node348_cert : Bound 7 := { allowed := (rows 32 80 96 16 0 0 0), upper := (rows 81 35 28 104 22 38 64), lower := (rows 81 35 28 104 16 32 64), losses := [] }

theorem profile34_node348 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,24,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,24,96] 6 6 profile34_node348_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,24,96] 6 6 profile34_node348_cert).mp (by decide +kernel))

def profile34_node342_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | _ => 0

def profile34_node342_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node342 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,24] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,24] 6 (by decide) (choices 2) [6,34,36,66,68,96] profile34_node342_route profile34_node342_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node343
  · exact profile34_node344
  · exact profile34_node345
  · exact profile34_node346
  · exact profile34_node347
  · exact profile34_node348

def profile34_node349_cert : CutBound 7 := { lost := (rows 32 0 16 32 0 0 0), upper := (rows 81 35 38 92 92 124 64), lower := (rows 81 35 38 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 65 103 102 72 64 96 64) },{ target := 5, region := (rows 21 2 4 12 20 0 127), good := (rows 81 67 95 72 81 64 64) }] }

theorem profile34_node349 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,34] 6 92 profile34_node349_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,34] 6 92 profile34_node349_cert).mp (by decide +kernel))

def profile34_node351_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 81 35 44 14 80 112 64), lower := (rows 81 35 44 14 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 32 127), good := (rows 65 111 108 78 64 96 64) }] }

theorem profile34_node351 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,40,6] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,40,6] 6 80 profile34_node351_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,40,6] 6 80 profile34_node351_cert).mp (by decide +kernel))

def profile34_node352_cert : Bound 7 := { allowed := (rows 32 80 64 96 0 0 0), upper := (rows 81 35 44 26 84 100 64), lower := (rows 81 35 44 26 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 44 127), good := (rows 65 99 108 110 64 96 64) }] }

theorem profile34_node352 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,40,18] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,40,18] 6 68 profile34_node352_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,40,18] 6 68 profile34_node352_cert).mp (by decide +kernel))

def profile34_node353_cert : Bound 7 := { allowed := (rows 32 64 80 96 0 0 0), upper := (rows 81 35 44 28 82 98 64), lower := (rows 81 35 44 28 16 32 64), losses := [{ target := 4, region := (rows 1 3 4 8 0 35 127), good := (rows 99 99 108 76 64 96 64) }] }

theorem profile34_node353 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,40,20] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,40,20] 6 66 profile34_node353_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,40,20] 6 66 profile34_node353_cert).mp (by decide +kernel))

def profile34_node354_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 81 35 44 74 20 52 64), lower := (rows 81 35 44 74 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 10 0 32 127), good := (rows 65 111 108 78 64 96 64) }] }

theorem profile34_node354 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,40,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,40,66] 6 20 profile34_node354_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,40,66] 6 20 profile34_node354_cert).mp (by decide +kernel))

def profile34_node355_cert : CutBound 7 := { lost := (rows 0 0 16 16 0 0 0), upper := (rows 81 35 44 76 18 50 64), lower := (rows 81 35 44 76 16 32 64), losses := [{ target := 4, region := (rows 1 2 38 46 0 32 127), good := (rows 65 111 108 76 64 108 64) }] }

theorem profile34_node355 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,40,68] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,40,68] 6 18 profile34_node355_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,40,68] 6 18 profile34_node355_cert).mp (by decide +kernel))

def profile34_node356_cert : Bound 7 := { allowed := (rows 32 80 80 32 0 0 0), upper := (rows 81 35 44 88 22 38 64), lower := (rows 81 35 44 88 16 32 64), losses := [] }

theorem profile34_node356 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,40,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,40,80] 6 6 profile34_node356_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,40,80] 6 6 profile34_node356_cert).mp (by decide +kernel))

def profile34_node350_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 34 => 5 | 36 => 5 | 48 => 5 | 96 => 5 | _ => 0

def profile34_node350_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node350 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,40] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,40] 6 (by decide) (choices 2) [6,18,20,66,68,80] profile34_node350_route profile34_node350_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node351
  · exact profile34_node352
  · exact profile34_node353
  · exact profile34_node354
  · exact profile34_node355
  · exact profile34_node356

def profile34_node357_cert : Bound 7 := { allowed := (rows 0 80 64 112 0 0 0), upper := (rows 81 35 52 78 94 110 64), lower := (rows 81 35 52 8 16 32 64), losses := [{ target := 5, region := (rows 21 2 4 8 16 0 127), good := (rows 81 67 85 72 81 64 64) }] }

theorem profile34_node357 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,48] 6 78 profile34_node357_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,48] 6 78 profile34_node357_cert).mp (by decide +kernel))

def profile34_node358_cert : CutBound 7 := { lost := (rows 32 0 48 0 0 0 0), upper := (rows 81 35 70 60 60 60 64), lower := (rows 81 35 70 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 6 8 0 32 127), good := (rows 65 103 70 72 64 96 64) },{ target := 5, region := (rows 17 2 6 8 16 0 127), good := (rows 81 71 70 72 81 64 64) }] }

theorem profile34_node358 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,66] 6 60 profile34_node358_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,66] 6 60 profile34_node358_cert).mp (by decide +kernel))

def profile34_node359_cert : CutBound 7 := { lost := (rows 32 0 48 0 0 0 0), upper := (rows 81 35 76 62 54 54 64), lower := (rows 81 35 76 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 12 8 0 32 127), good := (rows 65 99 76 76 64 96 64) },{ target := 5, region := (rows 17 2 12 8 16 0 127), good := (rows 81 67 76 76 81 64 64) }] }

theorem profile34_node359 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,72] 6 54 profile34_node359_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,72] 6 54 profile34_node359_cert).mp (by decide +kernel))

def profile34_node360_cert : CutBound 7 := { lost := (rows 32 0 32 0 0 0 0), upper := (rows 81 35 84 46 62 46 64), lower := (rows 81 35 84 8 16 32 64), losses := [{ target := 5, region := (rows 21 2 21 8 16 0 127), good := (rows 85 71 85 72 85 64 64) }] }

theorem profile34_node360 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,80] 6 46 profile34_node360_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,80] 6 46 profile34_node360_cert).mp (by decide +kernel))

def profile34_node361_cert : Bound 7 := { allowed := (rows 32 80 0 112 0 0 0), upper := (rows 81 35 100 30 30 62 64), lower := (rows 81 35 100 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 38 8 0 32 127), good := (rows 65 103 100 72 64 100 64) }] }

theorem profile34_node361 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,96] 6 30 profile34_node361_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33,96] 6 30 profile34_node361_cert).mp (by decide +kernel))

def profile34_node333_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | _ => 0

def profile34_node333_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node333 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,33] 6 (by decide) (choices 2) [10,18,24,34,40,48,66,72,80,96] profile34_node333_route profile34_node333_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node334
  · exact profile34_node341
  · exact profile34_node342
  · exact profile34_node349
  · exact profile34_node350
  · exact profile34_node357
  · exact profile34_node358
  · exact profile34_node359
  · exact profile34_node360
  · exact profile34_node361

def profile34_node364_cert : Bound 7 := { allowed := (rows 0 80 112 64 0 0 0), upper := (rows 81 38 7 56 88 104 64), lower := (rows 81 38 7 56 16 32 64), losses := [{ target := 5, region := (rows 25 2 4 8 24 0 127), good := (rows 81 70 71 89 81 64 64) }] }

theorem profile34_node364 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,3,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,3,48] 6 72 profile34_node364_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,3,48] 6 72 profile34_node364_cert).mp (by decide +kernel))

def profile34_node365_cert : CutBound 7 := { lost := (rows 32 0 0 32 0 0 0), upper := (rows 81 38 7 88 56 40 64), lower := (rows 81 38 7 88 16 32 64), losses := [{ target := 5, region := (rows 25 2 4 25 16 0 127), good := (rows 89 70 79 89 89 64 64) }] }

theorem profile34_node365 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,3,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,3,80] 6 40 profile34_node365_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,3,80] 6 40 profile34_node365_cert).mp (by decide +kernel))

def profile34_node366_cert : Bound 7 := { allowed := (rows 32 80 112 0 0 0 0), upper := (rows 81 38 7 104 24 56 64), lower := (rows 81 38 7 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 42 0 32 127), good := (rows 65 110 79 104 64 104 64) }] }

theorem profile34_node366 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,3,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,3,96] 6 24 profile34_node366_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,3,96] 6 24 profile34_node366_cert).mp (by decide +kernel))

def profile34_node363_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node363_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node363 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,3] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,3] 6 (by decide) (choices 2) [48,80,96] profile34_node363_route profile34_node363_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile34_node364
  · exact profile34_node365
  · exact profile34_node366

def profile34_node368_cert : CutBound 7 := { lost := (rows 32 16 32 0 0 0 0), upper := (rows 81 38 13 26 112 96 64), lower := (rows 81 38 13 26 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 127 127), good := (rows 97 102 111 106 96 96 96) },{ target := 5, region := (rows 25 2 12 8 16 0 127), good := (rows 81 70 77 95 81 64 64) }] }

theorem profile34_node368 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,9,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,9,18] 6 96 profile34_node368_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,9,18] 6 96 profile34_node368_cert).mp (by decide +kernel))

def profile34_node369_cert : CutBound 7 := { lost := (rows 32 0 32 16 0 0 0), upper := (rows 81 38 13 42 80 112 64), lower := (rows 81 38 13 42 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 32 127), good := (rows 65 110 77 106 64 96 64) },{ target := 5, region := (rows 127 2 12 8 127 0 127), good := (rows 81 87 93 95 81 81 81) }] }

theorem profile34_node369 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,9,34] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,9,34] 6 80 profile34_node369_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,9,34] 6 80 profile34_node369_cert).mp (by decide +kernel))

def profile34_node370_cert : Bound 7 := { allowed := (rows 32 64 112 64 0 0 0), upper := (rows 81 38 13 56 82 98 64), lower := (rows 81 38 13 56 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 38 127), good := (rows 65 102 111 104 64 96 64) }] }

theorem profile34_node370 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,9,48] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,9,48] 6 66 profile34_node370_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,9,48] 6 66 profile34_node370_cert).mp (by decide +kernel))

def profile34_node371_cert : CutBound 7 := { lost := (rows 32 0 0 48 0 0 0), upper := (rows 81 38 13 74 48 48 64), lower := (rows 81 38 13 74 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 32 127), good := (rows 65 110 77 74 64 96 64) },{ target := 5, region := (rows 17 2 4 10 16 0 127), good := (rows 81 78 77 74 81 64 64) }] }

theorem profile34_node371 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,9,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,9,66] 6 48 profile34_node371_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,9,66] 6 48 profile34_node371_cert).mp (by decide +kernel))

def profile34_node372_cert : Bound 7 := { allowed := (rows 32 64 112 32 0 0 0), upper := (rows 81 38 13 88 50 34 64), lower := (rows 81 38 13 88 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 38 127), good := (rows 65 102 111 72 64 96 64) }] }

theorem profile34_node372 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,9,80] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,9,80] 6 34 profile34_node372_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,9,80] 6 34 profile34_node372_cert).mp (by decide +kernel))

def profile34_node373_cert : Bound 7 := { allowed := (rows 32 80 112 0 0 0 0), upper := (rows 81 38 13 104 18 50 64), lower := (rows 81 38 13 104 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 42 0 32 127), good := (rows 65 110 77 104 64 104 64) }] }

theorem profile34_node373 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,9,96] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,9,96] 6 18 profile34_node373_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,9,96] 6 18 profile34_node373_cert).mp (by decide +kernel))

def profile34_node367_column : Nat → Fin 7 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node367_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node367 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,9] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,9] 6 (by decide) (choices 2) [18,34,48,66,80,96] profile34_node367_route profile34_node367_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node368
  · exact profile34_node369
  · exact profile34_node370
  · exact profile34_node371
  · exact profile34_node372
  · exact profile34_node373

def profile34_node375_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 81 38 14 25 112 96 64), lower := (rows 81 38 14 25 16 32 64), losses := [{ target := 4, region := (rows 1 14 12 8 0 127 127), good := (rows 97 102 110 111 96 96 96) }] }

theorem profile34_node375 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,10,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,10,17] 6 96 profile34_node375_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,10,17] 6 96 profile34_node375_cert).mp (by decide +kernel))

def profile34_node376_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 81 38 14 41 80 112 64), lower := (rows 81 38 14 41 16 32 64), losses := [{ target := 4, region := (rows 1 10 12 8 0 32 127), good := (rows 65 102 78 111 64 96 64) }] }

theorem profile34_node376 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,10,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,10,33] 6 80 profile34_node376_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,10,33] 6 80 profile34_node376_cert).mp (by decide +kernel))

def profile34_node377_cert : CutBound 7 := { lost := (rows 0 16 16 0 0 0 0), upper := (rows 81 38 14 56 81 97 64), lower := (rows 81 38 14 56 16 32 64), losses := [{ target := 4, region := (rows 1 10 12 8 0 33 127), good := (rows 97 102 78 110 64 96 64) }] }

theorem profile34_node377 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,10,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,10,48] 6 65 profile34_node377_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,10,48] 6 65 profile34_node377_cert).mp (by decide +kernel))

def profile34_node378_cert : CutBound 7 := { lost := (rows 32 0 0 48 0 0 0), upper := (rows 81 38 14 73 48 48 64), lower := (rows 81 38 14 73 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 32 127), good := (rows 73 102 78 73 64 96 64) },{ target := 5, region := (rows 17 2 4 25 16 0 127), good := (rows 89 70 78 73 89 64 64) }] }

theorem profile34_node378 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,10,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,10,65] 6 48 profile34_node378_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,10,65] 6 48 profile34_node378_cert).mp (by decide +kernel))

def profile34_node379_cert : CutBound 7 := { lost := (rows 32 0 0 32 0 0 0), upper := (rows 81 38 14 88 49 33 64), lower := (rows 81 38 14 88 16 32 64), losses := [{ target := 5, region := (rows 25 2 4 25 16 0 127), good := (rows 89 70 79 89 89 64 64) }] }

theorem profile34_node379 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,10,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,10,80] 6 33 profile34_node379_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,10,80] 6 33 profile34_node379_cert).mp (by decide +kernel))

def profile34_node380_cert : CutBound 7 := { lost := (rows 0 16 16 16 0 0 0), upper := (rows 81 38 14 104 17 49 64), lower := (rows 81 38 14 104 16 32 64), losses := [{ target := 4, region := (rows 1 42 46 42 0 32 127), good := (rows 65 110 78 110 64 110 64) }] }

theorem profile34_node380 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,10,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,10,96] 6 17 profile34_node380_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,10,96] 6 17 profile34_node380_cert).mp (by decide +kernel))

def profile34_node374_column : Nat → Fin 7 := fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | _ => 0

def profile34_node374_route : Route 7 := (fun mask => (mask,id))

theorem profile34_node374 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,10] 6 := by
  apply SmallFastRouting.sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,10] 6 (by decide) (choices 2) [17,33,48,65,80,96] profile34_node374_route profile34_node374_column
    (by change RowCover 7 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile34_node375
  · exact profile34_node376
  · exact profile34_node377
  · exact profile34_node378
  · exact profile34_node379
  · exact profile34_node380

def profile34_node381_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 81 38 21 106 122 106 64), lower := (rows 81 38 21 8 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 14 0 38 127), good := (rows 65 110 111 72 64 96 64) }] }

theorem profile34_node381 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,17] 6 106 profile34_node381_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,17] 6 106 profile34_node381_cert).mp (by decide +kernel))

def profile34_node382_cert : CutBound 7 := { lost := (rows 32 0 0 16 0 0 0), upper := (rows 81 38 22 105 121 105 64), lower := (rows 81 38 22 8 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 9 0 33 127), good := (rows 105 102 70 72 64 96 64) },{ target := 5, region := (rows 21 2 4 8 16 0 127), good := (rows 81 71 87 72 81 64 64) }] }

theorem profile34_node382 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,18] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,18] 6 105 profile34_node382_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,18] 6 105 profile34_node382_cert).mp (by decide +kernel))

def profile34_node384_cert : CutBound 7 := { lost := (rows 32 16 0 32 0 0 0), upper := (rows 81 38 28 11 112 96 64), lower := (rows 81 38 28 11 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 127 127), good := (rows 97 102 110 107 96 96 96) },{ target := 5, region := (rows 21 2 4 10 16 0 127), good := (rows 81 79 93 75 81 64 64) }] }

theorem profile34_node384 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,24,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,24,3] 6 96 profile34_node384_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,24,3] 6 96 profile34_node384_cert).mp (by decide +kernel))

def profile34_node385_cert : Bound 7 := { allowed := (rows 32 64 96 80 0 0 0), upper := (rows 81 38 28 41 82 98 64), lower := (rows 81 38 28 41 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 8 0 38 127), good := (rows 65 102 110 105 64 96 64) }] }

theorem profile34_node385 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,24,33] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,24,33] 6 66 profile34_node385_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,24,33] 6 66 profile34_node385_cert).mp (by decide +kernel))

def profile34_node386_cert : Bound 7 := { allowed := (rows 32 80 96 64 0 0 0), upper := (rows 81 38 28 42 81 97 64), lower := (rows 81 38 28 42 16 32 64), losses := [{ target := 4, region := (rows 1 2 4 10 0 33 127), good := (rows 97 110 76 106 64 96 64) }] }

theorem profile34_node386 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,24,34] 6 :=
  DegreeLoss.bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,24,34] 6 65 profile34_node386_cert
    ((DegreeLoss.boundCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,24,34] 6 65 profile34_node386_cert).mp (by decide +kernel))

def profile34_node387_cert : CutBound 7 := { lost := (rows 0 16 0 16 0 0 0), upper := (rows 81 38 28 73 50 34 64), lower := (rows 81 38 28 73 16 32 64), losses := [{ target := 4, region := (rows 1 6 4 9 0 38 127), good := (rows 73 102 110 73 64 96 64) }] }

theorem profile34_node387 : Upper (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,24,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,24,65] 6 34 profile34_node387_cert
    ((DegreeLoss.cutCheck_true (D (n:=7) [33,33,33,33,18,18,2]) (R (n:=7) [33,33,33,33,18,18,2]) [80,36,24,65] 6 34 profile34_node387_cert).mp (by decide +kernel))


#print axioms profile34_node387
end Delivery.SmallBudgetTenFinite7
