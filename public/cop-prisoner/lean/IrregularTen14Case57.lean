import IrregularTen14Base

namespace Delivery.IrregularTen14.Case57
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 224 224 240 224 0 0 0 0 0 0), upper := (rows 769 19 14 28 240 224 224 224 480 736), lower := (rows 769 19 14 28 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1023 2 4 8 0 1023 1023 1023 1023 1023), good := (rows 993 995 1007 1005 993 993 993 993 993 993) }] }

theorem upper_2 : Upper D R [768,17,10,20] 13 :=
  bound_sound D R [768,17,10,20] 13 bound_2
    ((Boolean.boundCheck_true D R [768,17,10,20] 13 bound_2).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 208 192 240 208 0 0 0 0 0 0), upper := (rows 769 19 14 44 48 240 208 208 464 720), lower := (rows 769 19 14 44 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 23 18 4 8 16 0 82 146 274 530), good := (rows 769 979 975 13 979 0 64 128 256 512) }] }

theorem upper_4 : Upper D R [768,17,10,36,32] 13 :=
  bound_sound D R [768,17,10,36,32] 13 bound_4
    ((Boolean.boundCheck_true D R [768,17,10,36,32] 13 bound_4).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 769 19 14 44 80 48 224 224 480 736), lower := (rows 769 19 14 44 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 45 2 4 8 0 32 104 168 296 552), good := (rows 769 3 975 1005 64 993 64 128 256 512) }] }

theorem upper_6 : Upper D R [768,17,10,36,64,16] 13 :=
  bound_sound D R [768,17,10,36,64,16] 13 bound_6
    ((Boolean.boundCheck_true D R [768,17,10,36,64,16] 13 bound_6).mp (by decide +kernel))

def bound_7 : Bound 10 := { allowed := (rows 240 224 224 192 0 0 0 0 0 0), upper := (rows 769 19 14 44 80 96 240 176 432 688), lower := (rows 769 19 14 44 80 96 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 6 10 0 112 64 128 256 512), good := (rows 769 47 14 44 96 96 96 128 256 512) }] }

theorem upper_7 : Upper D R [768,17,10,36,64,64] 13 :=
  bound_sound D R [768,17,10,36,64,64] 13 bound_7
    ((Boolean.boundCheck_true D R [768,17,10,36,64,64] 13 bound_7).mp (by decide +kernel))

def bound_9 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 769 19 14 44 80 160 80 224 480 736), lower := (rows 769 19 14 44 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 83 2 6 14 0 242 64 208 336 592), good := (rows 769 943 47 44 993 160 993 160 256 512) }] }

theorem upper_9 : Upper D R [768,17,10,36,64,128,16] 13 :=
  bound_sound D R [768,17,10,36,64,128,16] 13 bound_9
    ((Boolean.boundCheck_true D R [768,17,10,36,64,128,16] 13 bound_9).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 208 192 240 208 0 0 0 0 0 0), upper := (rows 769 19 14 44 80 160 96 208 464 720), lower := (rows 769 19 14 44 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 83 82 4 8 80 0 64 208 336 592), good := (rows 769 915 15 12 979 128 979 128 256 512) }] }

theorem upper_10 : Upper D R [768,17,10,36,64,128,32] 13 :=
  bound_sound D R [768,17,10,36,64,128,32] 13 bound_10
    ((Boolean.boundCheck_true D R [768,17,10,36,64,128,32] 13 bound_10).mp (by decide +kernel))

def bound_12 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 769 19 14 44 80 160 192 144 352 608), lower := (rows 769 19 14 44 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 255 2 4 8 0 224 224 128 504 760), good := (rows 769 771 783 877 865 993 993 993 256 512) }] }

theorem upper_12 : Upper D R [768,17,10,36,64,128,128,16] 13 :=
  bound_sound D R [768,17,10,36,64,128,128,16] 13 bound_12
    ((Boolean.boundCheck_true D R [768,17,10,36,64,128,128,16] 13 bound_12).mp (by decide +kernel))

def bound_13 : Bound 10 := { allowed := (rows 240 224 224 192 0 0 0 0 0 0), upper := (rows 769 19 14 44 80 160 192 160 336 592), lower := (rows 769 19 14 44 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 6 14 0 1023 1023 1023 256 512), good := (rows 993 239 238 236 224 224 224 224 480 736) }] }

theorem upper_13 : Upper D R [768,17,10,36,64,128,128,32] 13 :=
  bound_sound D R [768,17,10,36,64,128,128,32] 13 bound_13
    ((Boolean.boundCheck_true D R [768,17,10,36,64,128,128,32] 13 bound_13).mp (by decide +kernel))

def bound_14 : Bound 10 := { allowed := (rows 240 224 224 192 0 0 0 0 0 0), upper := (rows 769 19 14 44 80 160 192 192 304 560), lower := (rows 769 19 14 44 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 2 6 14 0 1023 1023 1023 256 512), good := (rows 993 239 238 236 224 224 224 224 480 736) }] }

theorem upper_14 : Upper D R [768,17,10,36,64,128,128,64] 13 :=
  bound_sound D R [768,17,10,36,64,128,128,64] 13 bound_14
    ((Boolean.boundCheck_true D R [768,17,10,36,64,128,128,64] 13 bound_14).mp (by decide +kernel))

def route_11 : Route 10 := (fun mask => (mask,id))

theorem upper_11 : Upper D R [768,17,10,36,64,128,128] 13 := by
  apply routed_branch D R [768,17,10,36,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_11
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,17,10,36,64,128,128] (choices 1) [16,32,64] route_11).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_12
  · exact upper_13
  · exact upper_14

def route_8 : Route 10 := (fun mask => (mask,id))

theorem upper_8 : Upper D R [768,17,10,36,64,128] 13 := by
  apply routed_branch D R [768,17,10,36,64,128] 13 (by decide) (choices 1) [16,32,128] route_8
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,17,10,36,64,128] (choices 1) [16,32,128] route_8).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_9
  · exact upper_10
  · exact upper_11

def route_5 : Route 10 := (fun mask => (mask,id))

theorem upper_5 : Upper D R [768,17,10,36,64] 13 := by
  apply routed_branch D R [768,17,10,36,64] 13 (by decide) (choices 1) [16,64,128] route_5
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,17,10,36,64] (choices 1) [16,64,128] route_5).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_6
  · exact upper_7
  · exact upper_8

def route_3 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_3 : Upper D R [768,17,10,36] 13 := by
  apply routed_branch D R [768,17,10,36] 13 (by decide) (choices 1) [32,64] route_3
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,17,10,36] (choices 1) [32,64] route_3).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_4
  · exact upper_5

def bound_15 : Bound 10 := { allowed := (rows 240 224 240 192 0 0 0 0 0 0), upper := (rows 769 19 14 56 244 228 228 228 484 740), lower := (rows 769 19 14 56 16 32 64 128 256 512), losses := [] }

theorem upper_15 : Upper D R [768,17,10,48] 13 :=
  bound_sound D R [768,17,10,48] 13 bound_15
    ((Boolean.boundCheck_true D R [768,17,10,48] 13 bound_15).mp (by decide +kernel))

def bound_16 : Bound 10 := { allowed := (rows 240 224 240 144 0 0 0 0 0 0), upper := (rows 769 19 14 104 244 244 244 244 500 756), lower := (rows 769 19 14 104 16 32 64 128 256 512), losses := [] }

theorem upper_16 : Upper D R [768,17,10,96] 13 :=
  bound_sound D R [768,17,10,96] 13 bound_16
    ((Boolean.boundCheck_true D R [768,17,10,96] 13 bound_16).mp (by decide +kernel))

def route_1 : Route 10 := (fun mask => match mask with | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [768,17,10] 13 := by
  apply routed_branch D R [768,17,10] 13 (by decide) (choices 2) [20,36,48,96] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [768,17,10] (choices 2) [20,36,48,96] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_15
  · exact upper_16

def bound_18 : Bound 10 := { allowed := (rows 240 224 224 208 0 0 0 0 0 0), upper := (rows 769 19 22 44 248 232 232 232 488 744), lower := (rows 769 19 22 44 16 32 64 128 256 512), losses := [] }

theorem upper_18 : Upper D R [768,17,18,36] 13 :=
  bound_sound D R [768,17,18,36] 13 bound_18
    ((Boolean.boundCheck_true D R [768,17,18,36] 13 bound_18).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 240 224 224 144 0 0 0 0 0 0), upper := (rows 769 19 22 104 252 236 236 236 492 748), lower := (rows 769 19 22 104 16 32 64 128 256 512), losses := [] }

theorem upper_19 : Upper D R [768,17,18,96] 13 :=
  bound_sound D R [768,17,18,96] 13 bound_19
    ((Boolean.boundCheck_true D R [768,17,18,96] 13 bound_19).mp (by decide +kernel))

def route_17 : Route 10 := (fun mask => match mask with | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_17 : Upper D R [768,17,18] 13 := by
  apply routed_branch D R [768,17,18] 13 (by decide) (choices 2) [36,96] route_17
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [768,17,18] (choices 2) [36,96] route_17).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_18
  · exact upper_19

def bound_21 : Bound 10 := { allowed := (rows 224 224 224 240 0 0 0 0 0 0), upper := (rows 769 19 28 14 240 224 224 224 480 736), lower := (rows 769 19 28 14 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1023 2 4 8 0 1023 1023 1023 1023 1023), good := (rows 993 995 1005 1007 993 993 993 993 993 993) }] }

theorem upper_21 : Upper D R [768,17,24,6] 13 :=
  bound_sound D R [768,17,24,6] 13 bound_21
    ((Boolean.boundCheck_true D R [768,17,24,6] 13 bound_21).mp (by decide +kernel))

def bound_22 : Bound 10 := { allowed := (rows 240 224 224 208 0 0 0 0 0 0), upper := (rows 769 19 28 42 244 228 228 228 484 740), lower := (rows 769 19 28 42 16 32 64 128 256 512), losses := [] }

theorem upper_22 : Upper D R [768,17,24,34] 13 :=
  bound_sound D R [768,17,24,34] 13 bound_22
    ((Boolean.boundCheck_true D R [768,17,24,34] 13 bound_22).mp (by decide +kernel))

def bound_23 : Bound 10 := { allowed := (rows 240 224 224 208 0 0 0 0 0 0), upper := (rows 769 19 28 44 242 226 226 226 482 738), lower := (rows 769 19 28 44 16 32 64 128 256 512), losses := [] }

theorem upper_23 : Upper D R [768,17,24,36] 13 :=
  bound_sound D R [768,17,24,36] 13 bound_23
    ((Boolean.boundCheck_true D R [768,17,24,36] 13 bound_23).mp (by decide +kernel))

def bound_24 : Bound 10 := { allowed := (rows 240 224 224 144 0 0 0 0 0 0), upper := (rows 769 19 28 104 246 230 230 230 486 742), lower := (rows 769 19 28 104 16 32 64 128 256 512), losses := [] }

theorem upper_24 : Upper D R [768,17,24,96] 13 :=
  bound_sound D R [768,17,24,96] 13 bound_24
    ((Boolean.boundCheck_true D R [768,17,24,96] 13 bound_24).mp (by decide +kernel))

def route_20 : Route 10 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_20 : Upper D R [768,17,24] 13 := by
  apply routed_branch D R [768,17,24] 13 (by decide) (choices 2) [6,34,36,96] route_20
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [768,17,24] (choices 2) [6,34,36,96] route_20).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_21
  · exact upper_22
  · exact upper_23
  · exact upper_24

def bound_26 : Bound 10 := { allowed := (rows 240 224 208 224 0 0 0 0 0 0), upper := (rows 769 19 38 28 248 232 232 232 488 744), lower := (rows 769 19 38 28 16 32 64 128 256 512), losses := [] }

theorem upper_26 : Upper D R [768,17,34,20] 13 :=
  bound_sound D R [768,17,34,20] 13 bound_26
    ((Boolean.boundCheck_true D R [768,17,34,20] 13 bound_26).mp (by decide +kernel))

def bound_27 : Bound 10 := { allowed := (rows 240 224 208 208 0 0 0 0 0 0), upper := (rows 769 19 38 44 216 248 216 216 472 728), lower := (rows 769 19 38 44 16 32 64 128 256 512), losses := [] }

theorem upper_27 : Upper D R [768,17,34,36] 13 :=
  bound_sound D R [768,17,34,36] 13 bound_27
    ((Boolean.boundCheck_true D R [768,17,34,36] 13 bound_27).mp (by decide +kernel))

def bound_28 : Bound 10 := { allowed := (rows 240 224 208 192 0 0 0 0 0 0), upper := (rows 769 19 38 56 220 236 204 204 460 716), lower := (rows 769 19 38 56 16 32 64 128 256 512), losses := [] }

theorem upper_28 : Upper D R [768,17,34,48] 13 :=
  bound_sound D R [768,17,34,48] 13 bound_28
    ((Boolean.boundCheck_true D R [768,17,34,48] 13 bound_28).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 240 224 208 176 0 0 0 0 0 0), upper := (rows 769 19 38 76 248 248 248 248 504 760), lower := (rows 769 19 38 76 16 32 64 128 256 512), losses := [] }

theorem upper_29 : Upper D R [768,17,34,68] 13 :=
  bound_sound D R [768,17,34,68] 13 bound_29
    ((Boolean.boundCheck_true D R [768,17,34,68] 13 bound_29).mp (by decide +kernel))

def bound_30 : Bound 10 := { allowed := (rows 240 224 208 160 0 0 0 0 0 0), upper := (rows 769 19 38 88 252 236 236 236 492 748), lower := (rows 769 19 38 88 16 32 64 128 256 512), losses := [] }

theorem upper_30 : Upper D R [768,17,34,80] 13 :=
  bound_sound D R [768,17,34,80] 13 bound_30
    ((Boolean.boundCheck_true D R [768,17,34,80] 13 bound_30).mp (by decide +kernel))

def bound_31 : Bound 10 := { allowed := (rows 240 224 208 144 0 0 0 0 0 0), upper := (rows 769 19 38 104 220 252 220 220 476 732), lower := (rows 769 19 38 104 16 32 64 128 256 512), losses := [] }

theorem upper_31 : Upper D R [768,17,34,96] 13 :=
  bound_sound D R [768,17,34,96] 13 bound_31
    ((Boolean.boundCheck_true D R [768,17,34,96] 13 bound_31).mp (by decide +kernel))

def bound_32 : Bound 10 := { allowed := (rows 240 224 208 48 0 0 0 0 0 0), upper := (rows 769 19 38 200 252 252 252 252 508 764), lower := (rows 769 19 38 200 16 32 64 128 256 512), losses := [] }

theorem upper_32 : Upper D R [768,17,34,192] 13 :=
  bound_sound D R [768,17,34,192] 13 bound_32
    ((Boolean.boundCheck_true D R [768,17,34,192] 13 bound_32).mp (by decide +kernel))

def route_25 : Route 10 := (fun mask => match mask with | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_25 : Upper D R [768,17,34] 13 := by
  apply routed_branch D R [768,17,34] 13 (by decide) (choices 2) [20,36,48,68,80,96,192] route_25
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [768,17,34] (choices 2) [20,36,48,68,80,96,192] route_25).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_26
  · exact upper_27
  · exact upper_28
  · exact upper_29
  · exact upper_30
  · exact upper_31
  · exact upper_32

def bound_35 : Bound 10 := { allowed := (rows 208 192 208 240 0 0 0 0 0 0), upper := (rows 769 19 44 14 48 240 208 208 464 720), lower := (rows 769 19 44 14 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 27 18 4 8 16 0 82 146 274 530), good := (rows 769 979 13 975 979 0 64 128 256 512) }] }

theorem upper_35 : Upper D R [768,17,40,6,32] 13 :=
  bound_sound D R [768,17,40,6,32] 13 bound_35
    ((Boolean.boundCheck_true D R [768,17,40,6,32] 13 bound_35).mp (by decide +kernel))

def bound_37 : Bound 10 := { allowed := (rows 224 224 208 240 0 0 0 0 0 0), upper := (rows 769 19 44 14 80 48 224 224 480 736), lower := (rows 769 19 44 14 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 45 2 4 8 0 32 100 164 292 548), good := (rows 769 3 1005 975 64 993 64 128 256 512) }] }

theorem upper_37 : Upper D R [768,17,40,6,64,16] 13 :=
  bound_sound D R [768,17,40,6,64,16] 13 bound_37
    ((Boolean.boundCheck_true D R [768,17,40,6,64,16] 13 bound_37).mp (by decide +kernel))

def bound_38 : Bound 10 := { allowed := (rows 240 224 192 224 0 0 0 0 0 0), upper := (rows 769 19 44 14 80 96 240 176 432 688), lower := (rows 769 19 44 14 80 96 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 6 10 0 112 64 128 256 512), good := (rows 769 47 44 14 96 96 96 128 256 512) }] }

theorem upper_38 : Upper D R [768,17,40,6,64,64] 13 :=
  bound_sound D R [768,17,40,6,64,64] 13 bound_38
    ((Boolean.boundCheck_true D R [768,17,40,6,64,64] 13 bound_38).mp (by decide +kernel))

def bound_40 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 769 19 44 14 80 160 80 224 480 736), lower := (rows 769 19 44 14 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 83 2 14 10 0 242 64 208 336 592), good := (rows 769 943 44 47 993 160 993 160 256 512) }] }

theorem upper_40 : Upper D R [768,17,40,6,64,128,16] 13 :=
  bound_sound D R [768,17,40,6,64,128,16] 13 bound_40
    ((Boolean.boundCheck_true D R [768,17,40,6,64,128,16] 13 bound_40).mp (by decide +kernel))

def bound_41 : Bound 10 := { allowed := (rows 208 192 208 240 0 0 0 0 0 0), upper := (rows 769 19 44 14 80 160 96 208 464 720), lower := (rows 769 19 44 14 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 83 82 4 8 80 0 64 208 336 592), good := (rows 769 915 12 15 979 128 979 128 256 512) }] }

theorem upper_41 : Upper D R [768,17,40,6,64,128,32] 13 :=
  bound_sound D R [768,17,40,6,64,128,32] 13 bound_41
    ((Boolean.boundCheck_true D R [768,17,40,6,64,128,32] 13 bound_41).mp (by decide +kernel))

def bound_43 : Bound 10 := { allowed := (rows 224 224 208 240 0 0 0 0 0 0), upper := (rows 769 19 44 14 80 160 192 144 352 608), lower := (rows 769 19 44 14 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 255 2 4 8 0 224 224 128 500 756), good := (rows 769 771 877 783 865 993 993 993 256 512) }] }

theorem upper_43 : Upper D R [768,17,40,6,64,128,128,16] 13 :=
  bound_sound D R [768,17,40,6,64,128,128,16] 13 bound_43
    ((Boolean.boundCheck_true D R [768,17,40,6,64,128,128,16] 13 bound_43).mp (by decide +kernel))

def bound_44 : Bound 10 := { allowed := (rows 240 224 192 224 0 0 0 0 0 0), upper := (rows 769 19 44 14 80 160 192 160 336 592), lower := (rows 769 19 44 14 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 14 10 0 1023 1023 1023 256 512), good := (rows 993 239 236 238 224 224 224 224 480 736) }] }

theorem upper_44 : Upper D R [768,17,40,6,64,128,128,32] 13 :=
  bound_sound D R [768,17,40,6,64,128,128,32] 13 bound_44
    ((Boolean.boundCheck_true D R [768,17,40,6,64,128,128,32] 13 bound_44).mp (by decide +kernel))

def bound_45 : Bound 10 := { allowed := (rows 240 224 192 224 0 0 0 0 0 0), upper := (rows 769 19 44 14 80 160 192 192 304 560), lower := (rows 769 19 44 14 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 2 14 10 0 1023 1023 1023 256 512), good := (rows 993 239 236 238 224 224 224 224 480 736) }] }

theorem upper_45 : Upper D R [768,17,40,6,64,128,128,64] 13 :=
  bound_sound D R [768,17,40,6,64,128,128,64] 13 bound_45
    ((Boolean.boundCheck_true D R [768,17,40,6,64,128,128,64] 13 bound_45).mp (by decide +kernel))

def route_42 : Route 10 := (fun mask => (mask,id))

theorem upper_42 : Upper D R [768,17,40,6,64,128,128] 13 := by
  apply routed_branch D R [768,17,40,6,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_42
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,17,40,6,64,128,128] (choices 1) [16,32,64] route_42).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_43
  · exact upper_44
  · exact upper_45

def route_39 : Route 10 := (fun mask => (mask,id))

theorem upper_39 : Upper D R [768,17,40,6,64,128] 13 := by
  apply routed_branch D R [768,17,40,6,64,128] 13 (by decide) (choices 1) [16,32,128] route_39
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,17,40,6,64,128] (choices 1) [16,32,128] route_39).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_40
  · exact upper_41
  · exact upper_42

def route_36 : Route 10 := (fun mask => (mask,id))

theorem upper_36 : Upper D R [768,17,40,6,64] 13 := by
  apply routed_branch D R [768,17,40,6,64] 13 (by decide) (choices 1) [16,64,128] route_36
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,17,40,6,64] (choices 1) [16,64,128] route_36).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_37
  · exact upper_38
  · exact upper_39

def route_34 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_34 : Upper D R [768,17,40,6] 13 := by
  apply routed_branch D R [768,17,40,6] 13 (by decide) (choices 1) [32,64] route_34
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,17,40,6] (choices 1) [32,64] route_34).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_35
  · exact upper_36

def bound_46 : Bound 10 := { allowed := (rows 240 224 208 224 0 0 0 0 0 0), upper := (rows 769 19 44 26 244 228 228 228 484 740), lower := (rows 769 19 44 26 16 32 64 128 256 512), losses := [] }

theorem upper_46 : Upper D R [768,17,40,18] 13 :=
  bound_sound D R [768,17,40,18] 13 bound_46
    ((Boolean.boundCheck_true D R [768,17,40,18] 13 bound_46).mp (by decide +kernel))

def bound_47 : Bound 10 := { allowed := (rows 240 224 208 224 0 0 0 0 0 0), upper := (rows 769 19 44 28 242 226 226 226 482 738), lower := (rows 769 19 44 28 16 32 64 128 256 512), losses := [] }

theorem upper_47 : Upper D R [768,17,40,20] 13 :=
  bound_sound D R [768,17,40,20] 13 bound_47
    ((Boolean.boundCheck_true D R [768,17,40,20] 13 bound_47).mp (by decide +kernel))

def bound_48 : Bound 10 := { allowed := (rows 240 224 208 208 0 0 0 0 0 0), upper := (rows 769 19 44 42 212 244 212 212 468 724), lower := (rows 769 19 44 42 16 32 64 128 256 512), losses := [] }

theorem upper_48 : Upper D R [768,17,40,34] 13 :=
  bound_sound D R [768,17,40,34] 13 bound_48
    ((Boolean.boundCheck_true D R [768,17,40,34] 13 bound_48).mp (by decide +kernel))

def bound_49 : Bound 10 := { allowed := (rows 240 224 208 208 0 0 0 0 0 0), upper := (rows 769 19 44 44 210 242 210 210 466 722), lower := (rows 769 19 44 44 16 32 64 128 256 512), losses := [] }

theorem upper_49 : Upper D R [768,17,40,36] 13 :=
  bound_sound D R [768,17,40,36] 13 bound_49
    ((Boolean.boundCheck_true D R [768,17,40,36] 13 bound_49).mp (by decide +kernel))

def bound_50 : Bound 10 := { allowed := (rows 240 224 208 192 0 0 0 0 0 0), upper := (rows 769 19 44 56 214 230 198 198 454 710), lower := (rows 769 19 44 56 16 32 64 128 256 512), losses := [] }

theorem upper_50 : Upper D R [768,17,40,48] 13 :=
  bound_sound D R [768,17,40,48] 13 bound_50
    ((Boolean.boundCheck_true D R [768,17,40,48] 13 bound_50).mp (by decide +kernel))

def bound_51 : Bound 10 := { allowed := (rows 240 224 208 176 0 0 0 0 0 0), upper := (rows 769 19 44 74 244 244 244 244 500 756), lower := (rows 769 19 44 74 16 32 64 128 256 512), losses := [] }

theorem upper_51 : Upper D R [768,17,40,66] 13 :=
  bound_sound D R [768,17,40,66] 13 bound_51
    ((Boolean.boundCheck_true D R [768,17,40,66] 13 bound_51).mp (by decide +kernel))

def bound_52 : Bound 10 := { allowed := (rows 240 224 208 176 0 0 0 0 0 0), upper := (rows 769 19 44 76 242 242 242 242 498 754), lower := (rows 769 19 44 76 16 32 64 128 256 512), losses := [] }

theorem upper_52 : Upper D R [768,17,40,68] 13 :=
  bound_sound D R [768,17,40,68] 13 bound_52
    ((Boolean.boundCheck_true D R [768,17,40,68] 13 bound_52).mp (by decide +kernel))

def bound_53 : Bound 10 := { allowed := (rows 240 224 208 160 0 0 0 0 0 0), upper := (rows 769 19 44 88 246 230 230 230 486 742), lower := (rows 769 19 44 88 16 32 64 128 256 512), losses := [] }

theorem upper_53 : Upper D R [768,17,40,80] 13 :=
  bound_sound D R [768,17,40,80] 13 bound_53
    ((Boolean.boundCheck_true D R [768,17,40,80] 13 bound_53).mp (by decide +kernel))

def bound_54 : Bound 10 := { allowed := (rows 240 224 208 144 0 0 0 0 0 0), upper := (rows 769 19 44 104 214 246 214 214 470 726), lower := (rows 769 19 44 104 16 32 64 128 256 512), losses := [] }

theorem upper_54 : Upper D R [768,17,40,96] 13 :=
  bound_sound D R [768,17,40,96] 13 bound_54
    ((Boolean.boundCheck_true D R [768,17,40,96] 13 bound_54).mp (by decide +kernel))

def bound_55 : Bound 10 := { allowed := (rows 240 224 208 48 0 0 0 0 0 0), upper := (rows 769 19 44 200 246 246 246 246 502 758), lower := (rows 769 19 44 200 16 32 64 128 256 512), losses := [] }

theorem upper_55 : Upper D R [768,17,40,192] 13 :=
  bound_sound D R [768,17,40,192] 13 bound_55
    ((Boolean.boundCheck_true D R [768,17,40,192] 13 bound_55).mp (by decide +kernel))

def route_33 : Route 10 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_33 : Upper D R [768,17,40] 13 := by
  apply routed_branch D R [768,17,40] 13 (by decide) (choices 2) [6,18,20,34,36,48,66,68,80,96,192] route_33
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [768,17,40] (choices 2) [6,18,20,34,36,48,66,68,80,96,192] route_33).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_34
  · exact upper_46
  · exact upper_47
  · exact upper_48
  · exact upper_49
  · exact upper_50
  · exact upper_51
  · exact upper_52
  · exact upper_53
  · exact upper_54
  · exact upper_55

def bound_56 : Bound 10 := { allowed := (rows 240 224 192 240 0 0 0 0 0 0), upper := (rows 769 19 52 238 254 238 238 238 494 750), lower := (rows 769 19 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_56 : Upper D R [768,17,48] 13 :=
  bound_sound D R [768,17,48] 13 bound_56
    ((Boolean.boundCheck_true D R [768,17,48] 13 bound_56).mp (by decide +kernel))

def bound_57 : Bound 10 := { allowed := (rows 240 224 144 240 0 0 0 0 0 0), upper := (rows 769 19 100 254 254 254 254 254 510 766), lower := (rows 769 19 100 8 16 32 64 128 256 512), losses := [] }

theorem upper_57 : Upper D R [768,17,96] 13 :=
  bound_sound D R [768,17,96] 13 bound_57
    ((Boolean.boundCheck_true D R [768,17,96] 13 bound_57).mp (by decide +kernel))

def route_0 : Route 10 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [768,17] 13 := by
  apply routed_branch D R [768,17] 13 (by decide) (choices 2) [10,18,24,34,40,48,96] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [768,17] (choices 2) [10,18,24,34,40,48,96] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_17
  · exact upper_20
  · exact upper_25
  · exact upper_33
  · exact upper_56
  · exact upper_57

theorem upper : Upper D R [768,17] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case57
