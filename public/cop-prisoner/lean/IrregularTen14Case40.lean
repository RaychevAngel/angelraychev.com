import IrregularTen14Base

namespace Delivery.IrregularTen14.Case40
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 224 224 224 224 0 0 0 0 0 0), upper := (rows 259 515 28 28 240 224 224 224 480 736), lower := (rows 259 515 28 28 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1023 1023 4 8 0 1023 1023 1023 1023 1023), good := (rows 995 995 1007 1007 995 995 995 995 995 995) }] }

theorem upper_2 : Upper D R [258,513,24,20] 13 :=
  bound_sound D R [258,513,24,20] 13 bound_2
    ((Boolean.boundCheck_true D R [258,513,24,20] 13 bound_2).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 208 208 224 208 0 0 0 0 0 0), upper := (rows 259 515 28 44 48 240 208 208 464 720), lower := (rows 259 515 28 44 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 29 30 4 8 16 0 84 148 276 532), good := (rows 259 515 991 975 979 0 64 128 256 512) }] }

theorem upper_4 : Upper D R [258,513,24,36,32] 13 :=
  bound_sound D R [258,513,24,36,32] 13 bound_4
    ((Boolean.boundCheck_true D R [258,513,24,36,32] 13 bound_4).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 224 224 224 208 0 0 0 0 0 0), upper := (rows 259 515 28 44 80 48 224 224 480 736), lower := (rows 259 515 28 44 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 45 46 4 8 0 32 104 168 296 552), good := (rows 259 515 975 1007 64 995 64 128 256 512) }] }

theorem upper_6 : Upper D R [258,513,24,36,64,16] 13 :=
  bound_sound D R [258,513,24,36,64,16] 13 bound_6
    ((Boolean.boundCheck_true D R [258,513,24,36,64,16] 13 bound_6).mp (by decide +kernel))

def bound_7 : Bound 10 := { allowed := (rows 240 240 224 192 0 0 0 0 0 0), upper := (rows 259 515 28 44 80 96 240 176 432 688), lower := (rows 259 515 28 44 80 96 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 12 0 112 64 128 256 512), good := (rows 259 515 44 44 96 96 96 128 256 512) }] }

theorem upper_7 : Upper D R [258,513,24,36,64,64] 13 :=
  bound_sound D R [258,513,24,36,64,64] 13 bound_7
    ((Boolean.boundCheck_true D R [258,513,24,36,64,64] 13 bound_7).mp (by decide +kernel))

def bound_9 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 259 515 28 44 80 160 80 224 480 736), lower := (rows 259 515 28 44 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 85 86 4 12 0 244 64 208 336 592), good := (rows 259 515 943 47 995 160 995 160 256 512) }] }

theorem upper_9 : Upper D R [258,513,24,36,64,128,16] 13 :=
  bound_sound D R [258,513,24,36,64,128,16] 13 bound_9
    ((Boolean.boundCheck_true D R [258,513,24,36,64,128,16] 13 bound_9).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 208 208 224 208 0 0 0 0 0 0), upper := (rows 259 515 28 44 80 160 96 208 464 720), lower := (rows 259 515 28 44 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 85 86 4 8 80 0 64 208 336 592), good := (rows 259 515 927 15 979 128 979 128 256 512) }] }

theorem upper_10 : Upper D R [258,513,24,36,64,128,32] 13 :=
  bound_sound D R [258,513,24,36,64,128,32] 13 bound_10
    ((Boolean.boundCheck_true D R [258,513,24,36,64,128,32] 13 bound_10).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 240 240 192 208 0 0 0 0 0 0), upper := (rows 259 515 28 44 80 160 192 240 368 624), lower := (rows 259 515 28 44 80 160 192 128 256 512), losses := [{ target := 5, region := (rows 1 2 12 8 248 0 224 128 256 512), good := (rows 259 515 28 92 80 208 208 208 256 512) }] }

theorem upper_11 : Upper D R [258,513,24,36,64,128,128] 13 :=
  bound_sound D R [258,513,24,36,64,128,128] 13 bound_11
    ((Boolean.boundCheck_true D R [258,513,24,36,64,128,128] 13 bound_11).mp (by decide +kernel))

def route_8 : Route 10 := (fun mask => (mask,id))

theorem upper_8 : Upper D R [258,513,24,36,64,128] 13 := by
  apply routed_branch D R [258,513,24,36,64,128] 13 (by decide) (choices 1) [16,32,128] route_8
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,513,24,36,64,128] (choices 1) [16,32,128] route_8).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_9
  · exact upper_10
  · exact upper_11

def route_5 : Route 10 := (fun mask => (mask,id))

theorem upper_5 : Upper D R [258,513,24,36,64] 13 := by
  apply routed_branch D R [258,513,24,36,64] 13 (by decide) (choices 1) [16,64,128] route_5
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,513,24,36,64] (choices 1) [16,64,128] route_5).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_6
  · exact upper_7
  · exact upper_8

def route_3 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_3 : Upper D R [258,513,24,36] 13 := by
  apply routed_branch D R [258,513,24,36] 13 (by decide) (choices 1) [32,64] route_3
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,513,24,36] (choices 1) [32,64] route_3).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_4
  · exact upper_5

def bound_12 : Bound 10 := { allowed := (rows 240 240 224 192 0 0 0 0 0 0), upper := (rows 259 515 28 56 244 228 228 228 484 740), lower := (rows 259 515 28 56 16 32 64 128 256 512), losses := [] }

theorem upper_12 : Upper D R [258,513,24,48] 13 :=
  bound_sound D R [258,513,24,48] 13 bound_12
    ((Boolean.boundCheck_true D R [258,513,24,48] 13 bound_12).mp (by decide +kernel))

def bound_13 : Bound 10 := { allowed := (rows 240 240 224 144 0 0 0 0 0 0), upper := (rows 259 515 28 104 244 244 244 244 500 756), lower := (rows 259 515 28 104 16 32 64 128 256 512), losses := [] }

theorem upper_13 : Upper D R [258,513,24,96] 13 :=
  bound_sound D R [258,513,24,96] 13 bound_13
    ((Boolean.boundCheck_true D R [258,513,24,96] 13 bound_13).mp (by decide +kernel))

def route_1 : Route 10 := (fun mask => match mask with | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [258,513,24] 13 := by
  apply routed_branch D R [258,513,24] 13 (by decide) (choices 2) [20,36,48,96] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,513,24] (choices 2) [20,36,48,96] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_12
  · exact upper_13

def bound_15 : Bound 10 := { allowed := (rows 240 240 192 224 0 0 0 0 0 0), upper := (rows 259 515 52 28 248 232 232 232 488 744), lower := (rows 259 515 52 28 16 32 64 128 256 512), losses := [] }

theorem upper_15 : Upper D R [258,513,48,20] 13 :=
  bound_sound D R [258,513,48,20] 13 bound_15
    ((Boolean.boundCheck_true D R [258,513,48,20] 13 bound_15).mp (by decide +kernel))

def bound_16 : Bound 10 := { allowed := (rows 240 240 192 192 0 0 0 0 0 0), upper := (rows 259 515 52 56 220 236 204 204 460 716), lower := (rows 259 515 52 56 16 32 64 128 256 512), losses := [] }

theorem upper_16 : Upper D R [258,513,48,48] 13 :=
  bound_sound D R [258,513,48,48] 13 bound_16
    ((Boolean.boundCheck_true D R [258,513,48,48] 13 bound_16).mp (by decide +kernel))

def bound_17 : Bound 10 := { allowed := (rows 240 240 192 176 0 0 0 0 0 0), upper := (rows 259 515 52 76 248 248 248 248 504 760), lower := (rows 259 515 52 76 16 32 64 128 256 512), losses := [] }

theorem upper_17 : Upper D R [258,513,48,68] 13 :=
  bound_sound D R [258,513,48,68] 13 bound_17
    ((Boolean.boundCheck_true D R [258,513,48,68] 13 bound_17).mp (by decide +kernel))

def bound_18 : Bound 10 := { allowed := (rows 240 240 192 160 0 0 0 0 0 0), upper := (rows 259 515 52 88 252 236 236 236 492 748), lower := (rows 259 515 52 88 16 32 64 128 256 512), losses := [] }

theorem upper_18 : Upper D R [258,513,48,80] 13 :=
  bound_sound D R [258,513,48,80] 13 bound_18
    ((Boolean.boundCheck_true D R [258,513,48,80] 13 bound_18).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 240 240 192 48 0 0 0 0 0 0), upper := (rows 259 515 52 200 252 252 252 252 508 764), lower := (rows 259 515 52 200 16 32 64 128 256 512), losses := [] }

theorem upper_19 : Upper D R [258,513,48,192] 13 :=
  bound_sound D R [258,513,48,192] 13 bound_19
    ((Boolean.boundCheck_true D R [258,513,48,192] 13 bound_19).mp (by decide +kernel))

def route_14 : Route 10 := (fun mask => match mask with | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_14 : Upper D R [258,513,48] 13 := by
  apply routed_branch D R [258,513,48] 13 (by decide) (choices 2) [20,48,68,80,192] route_14
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,513,48] (choices 2) [20,48,68,80,192] route_14).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact upper_15
  · exact upper_16
  · exact upper_17
  · exact upper_18
  · exact upper_19

def route_0 : Route 10 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 136 => (24,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [258,513] 13 := by
  apply routed_branch D R [258,513] 13 (by decide) (choices 2) [24,48] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,513] (choices 2) [24,48] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_1
  · exact upper_14

theorem upper : Upper D R [258,513] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case40
