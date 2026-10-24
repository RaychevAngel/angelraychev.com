import IrregularTen14Base

namespace Delivery.IrregularTen14.Case55
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_3 : Bound 10 := { allowed := (rows 208 208 208 192 0 0 0 0 0 0), upper := (rows 769 7 14 56 48 240 208 208 464 720), lower := (rows 769 7 14 56 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 29 14 12 8 16 0 88 152 280 536), good := (rows 769 7 975 991 977 0 64 128 256 512) }] }

theorem upper_3 : Upper D R [768,5,10,48,32] 13 :=
  bound_sound D R [768,5,10,48,32] 13 bound_3
    ((Boolean.boundCheck_true D R [768,5,10,48,32] 13 bound_3).mp (by decide +kernel))

def bound_5 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 769 7 14 56 80 48 224 224 480 736), lower := (rows 769 7 14 56 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 45 14 12 8 0 32 104 168 296 552), good := (rows 769 7 975 1007 64 993 64 128 256 512) }] }

theorem upper_5 : Upper D R [768,5,10,48,64,16] 13 :=
  bound_sound D R [768,5,10,48,64,16] 13 bound_5
    ((Boolean.boundCheck_true D R [768,5,10,48,64,16] 13 bound_5).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 176 176 176 192 0 0 0 0 0 0), upper := (rows 769 7 14 56 80 96 240 176 432 688), lower := (rows 769 7 14 56 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 13 14 12 8 16 32 0 136 264 520), good := (rows 769 7 911 959 16 32 0 128 256 512) }] }

theorem upper_6 : Upper D R [768,5,10,48,64,64] 13 :=
  bound_sound D R [768,5,10,48,64,64] 13 bound_6
    ((Boolean.boundCheck_true D R [768,5,10,48,64,64] 13 bound_6).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 769 7 14 56 80 160 80 224 480 736), lower := (rows 769 7 14 56 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 89 14 12 8 0 248 64 208 336 592), good := (rows 769 7 47 943 993 160 993 160 256 512) }] }

theorem upper_8 : Upper D R [768,5,10,48,64,128,16] 13 :=
  bound_sound D R [768,5,10,48,64,128,16] 13 bound_8
    ((Boolean.boundCheck_true D R [768,5,10,48,64,128,16] 13 bound_8).mp (by decide +kernel))

def bound_9 : Bound 10 := { allowed := (rows 208 208 208 192 0 0 0 0 0 0), upper := (rows 769 7 14 56 80 160 96 208 464 720), lower := (rows 769 7 14 56 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 89 14 12 8 80 0 64 208 336 592), good := (rows 769 7 15 927 977 128 977 128 256 512) }] }

theorem upper_9 : Upper D R [768,5,10,48,64,128,32] 13 :=
  bound_sound D R [768,5,10,48,64,128,32] 13 bound_9
    ((Boolean.boundCheck_true D R [768,5,10,48,64,128,32] 13 bound_9).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 240 240 240 128 0 0 0 0 0 0), upper := (rows 769 7 14 56 80 160 192 240 368 624), lower := (rows 769 7 14 56 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 1 2 4 24 16 224 0 128 256 512), good := (rows 769 7 14 56 56 160 160 160 256 512) }] }

theorem upper_10 : Upper D R [768,5,10,48,64,128,128] 13 :=
  bound_sound D R [768,5,10,48,64,128,128] 13 bound_10
    ((Boolean.boundCheck_true D R [768,5,10,48,64,128,128] 13 bound_10).mp (by decide +kernel))

def route_7 : Route 10 := (fun mask => (mask,id))

theorem upper_7 : Upper D R [768,5,10,48,64,128] 13 := by
  apply routed_branch D R [768,5,10,48,64,128] 13 (by decide) (choices 1) [16,32,128] route_7
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,5,10,48,64,128] (choices 1) [16,32,128] route_7).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_8
  · exact upper_9
  · exact upper_10

def route_4 : Route 10 := (fun mask => (mask,id))

theorem upper_4 : Upper D R [768,5,10,48,64] 13 := by
  apply routed_branch D R [768,5,10,48,64] 13 (by decide) (choices 1) [16,64,128] route_4
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,5,10,48,64] (choices 1) [16,64,128] route_4).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_5
  · exact upper_6
  · exact upper_7

def route_2 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_2 : Upper D R [768,5,10,48] 13 := by
  apply routed_branch D R [768,5,10,48] 13 (by decide) (choices 1) [32,64] route_2
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,5,10,48] (choices 1) [32,64] route_2).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_3
  · exact upper_4

def route_1 : Route 10 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [768,5,10] 13 := by
  apply routed_branch D R [768,5,10] 13 (by decide) (choices 2) [48] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [768,5,10] (choices 2) [48] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  · exact upper_2

def bound_12 : Bound 10 := { allowed := (rows 240 240 224 192 0 0 0 0 0 0), upper := (rows 769 7 22 56 248 232 232 232 488 744), lower := (rows 769 7 22 56 16 32 64 128 256 512), losses := [] }

theorem upper_12 : Upper D R [768,5,18,48] 13 :=
  bound_sound D R [768,5,18,48] 13 bound_12
    ((Boolean.boundCheck_true D R [768,5,18,48] 13 bound_12).mp (by decide +kernel))

def bound_13 : Bound 10 := { allowed := (rows 240 240 224 144 0 0 0 0 0 0), upper := (rows 769 7 22 104 248 248 248 248 504 760), lower := (rows 769 7 22 104 16 32 64 128 256 512), losses := [] }

theorem upper_13 : Upper D R [768,5,18,96] 13 :=
  bound_sound D R [768,5,18,96] 13 bound_13
    ((Boolean.boundCheck_true D R [768,5,18,96] 13 bound_13).mp (by decide +kernel))

def route_11 : Route 10 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_11 : Upper D R [768,5,18] 13 := by
  apply routed_branch D R [768,5,18] 13 (by decide) (choices 2) [48,96] route_11
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [768,5,18] (choices 2) [48,96] route_11).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_12
  · exact upper_13

def bound_15 : Bound 10 := { allowed := (rows 224 224 224 224 0 0 0 0 0 0), upper := (rows 769 7 28 26 240 224 224 224 480 736), lower := (rows 769 7 28 26 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1023 6 4 8 0 1023 1023 1023 1023 1023), good := (rows 993 999 1007 1003 993 993 993 993 993 993) }] }

theorem upper_15 : Upper D R [768,5,24,18] 13 :=
  bound_sound D R [768,5,24,18] 13 bound_15
    ((Boolean.boundCheck_true D R [768,5,24,18] 13 bound_15).mp (by decide +kernel))

def bound_17 : Bound 10 := { allowed := (rows 208 208 224 208 0 0 0 0 0 0), upper := (rows 769 7 28 42 48 240 208 208 464 720), lower := (rows 769 7 28 42 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 23 6 4 8 16 0 84 148 276 532), good := (rows 769 967 991 11 977 0 64 128 256 512) }] }

theorem upper_17 : Upper D R [768,5,24,34,32] 13 :=
  bound_sound D R [768,5,24,34,32] 13 bound_17
    ((Boolean.boundCheck_true D R [768,5,24,34,32] 13 bound_17).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 224 224 224 208 0 0 0 0 0 0), upper := (rows 769 7 28 42 80 48 224 224 480 736), lower := (rows 769 7 28 42 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 45 6 4 8 0 32 104 168 296 552), good := (rows 769 7 975 1003 64 993 64 128 256 512) }] }

theorem upper_19 : Upper D R [768,5,24,34,64,16] 13 :=
  bound_sound D R [768,5,24,34,64,16] 13 bound_19
    ((Boolean.boundCheck_true D R [768,5,24,34,64,16] 13 bound_19).mp (by decide +kernel))

def bound_20 : Bound 10 := { allowed := (rows 240 240 192 208 0 0 0 0 0 0), upper := (rows 769 7 28 42 80 96 240 176 432 688), lower := (rows 769 7 28 42 80 96 64 128 256 512), losses := [{ target := 5, region := (rows 1 2 12 8 112 0 64 128 256 512), good := (rows 769 7 28 30 80 80 80 128 256 512) }] }

theorem upper_20 : Upper D R [768,5,24,34,64,64] 13 :=
  bound_sound D R [768,5,24,34,64,64] 13 bound_20
    ((Boolean.boundCheck_true D R [768,5,24,34,64,64] 13 bound_20).mp (by decide +kernel))

def bound_22 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 769 7 28 42 80 160 80 224 480 736), lower := (rows 769 7 28 42 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 85 6 4 14 0 244 64 208 336 592), good := (rows 769 47 943 42 993 160 993 160 256 512) }] }

theorem upper_22 : Upper D R [768,5,24,34,64,128,16] 13 :=
  bound_sound D R [768,5,24,34,64,128,16] 13 bound_22
    ((Boolean.boundCheck_true D R [768,5,24,34,64,128,16] 13 bound_22).mp (by decide +kernel))

def bound_23 : Bound 10 := { allowed := (rows 208 208 224 208 0 0 0 0 0 0), upper := (rows 769 7 28 42 80 160 96 208 464 720), lower := (rows 769 7 28 42 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 85 6 4 8 80 0 64 208 336 592), good := (rows 769 7 927 10 977 128 977 128 256 512) }] }

theorem upper_23 : Upper D R [768,5,24,34,64,128,32] 13 :=
  bound_sound D R [768,5,24,34,64,128,32] 13 bound_23
    ((Boolean.boundCheck_true D R [768,5,24,34,64,128,32] 13 bound_23).mp (by decide +kernel))

def bound_24 : Bound 10 := { allowed := (rows 240 240 192 208 0 0 0 0 0 0), upper := (rows 769 7 28 42 80 160 192 240 368 624), lower := (rows 769 7 28 42 80 160 192 128 256 512), losses := [{ target := 5, region := (rows 1 2 12 8 248 0 224 128 256 512), good := (rows 769 7 28 94 80 208 208 208 256 512) }] }

theorem upper_24 : Upper D R [768,5,24,34,64,128,128] 13 :=
  bound_sound D R [768,5,24,34,64,128,128] 13 bound_24
    ((Boolean.boundCheck_true D R [768,5,24,34,64,128,128] 13 bound_24).mp (by decide +kernel))

def route_21 : Route 10 := (fun mask => (mask,id))

theorem upper_21 : Upper D R [768,5,24,34,64,128] 13 := by
  apply routed_branch D R [768,5,24,34,64,128] 13 (by decide) (choices 1) [16,32,128] route_21
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,5,24,34,64,128] (choices 1) [16,32,128] route_21).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_22
  · exact upper_23
  · exact upper_24

def route_18 : Route 10 := (fun mask => (mask,id))

theorem upper_18 : Upper D R [768,5,24,34,64] 13 := by
  apply routed_branch D R [768,5,24,34,64] 13 (by decide) (choices 1) [16,64,128] route_18
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,5,24,34,64] (choices 1) [16,64,128] route_18).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_19
  · exact upper_20
  · exact upper_21

def route_16 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_16 : Upper D R [768,5,24,34] 13 := by
  apply routed_branch D R [768,5,24,34] 13 (by decide) (choices 1) [32,64] route_16
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [768,5,24,34] (choices 1) [32,64] route_16).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_17
  · exact upper_18

def bound_25 : Bound 10 := { allowed := (rows 240 240 224 192 0 0 0 0 0 0), upper := (rows 769 7 28 56 242 226 226 226 482 738), lower := (rows 769 7 28 56 16 32 64 128 256 512), losses := [] }

theorem upper_25 : Upper D R [768,5,24,48] 13 :=
  bound_sound D R [768,5,24,48] 13 bound_25
    ((Boolean.boundCheck_true D R [768,5,24,48] 13 bound_25).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 240 240 224 144 0 0 0 0 0 0), upper := (rows 769 7 28 104 242 242 242 242 498 754), lower := (rows 769 7 28 104 16 32 64 128 256 512), losses := [] }

theorem upper_26 : Upper D R [768,5,24,96] 13 :=
  bound_sound D R [768,5,24,96] 13 bound_26
    ((Boolean.boundCheck_true D R [768,5,24,96] 13 bound_26).mp (by decide +kernel))

def route_14 : Route 10 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_14 : Upper D R [768,5,24] 13 := by
  apply routed_branch D R [768,5,24] 13 (by decide) (choices 2) [18,34,48,96] route_14
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [768,5,24] (choices 2) [18,34,48,96] route_14).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_15
  · exact upper_16
  · exact upper_25
  · exact upper_26

def bound_28 : Bound 10 := { allowed := (rows 240 240 192 224 0 0 0 0 0 0), upper := (rows 769 7 52 26 248 232 232 232 488 744), lower := (rows 769 7 52 26 16 32 64 128 256 512), losses := [] }

theorem upper_28 : Upper D R [768,5,48,18] 13 :=
  bound_sound D R [768,5,48,18] 13 bound_28
    ((Boolean.boundCheck_true D R [768,5,48,18] 13 bound_28).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 240 240 192 192 0 0 0 0 0 0), upper := (rows 769 7 52 56 218 234 202 202 458 714), lower := (rows 769 7 52 56 16 32 64 128 256 512), losses := [] }

theorem upper_29 : Upper D R [768,5,48,48] 13 :=
  bound_sound D R [768,5,48,48] 13 bound_29
    ((Boolean.boundCheck_true D R [768,5,48,48] 13 bound_29).mp (by decide +kernel))

def bound_30 : Bound 10 := { allowed := (rows 240 240 192 176 0 0 0 0 0 0), upper := (rows 769 7 52 74 248 248 248 248 504 760), lower := (rows 769 7 52 74 16 32 64 128 256 512), losses := [] }

theorem upper_30 : Upper D R [768,5,48,66] 13 :=
  bound_sound D R [768,5,48,66] 13 bound_30
    ((Boolean.boundCheck_true D R [768,5,48,66] 13 bound_30).mp (by decide +kernel))

def bound_31 : Bound 10 := { allowed := (rows 240 240 192 160 0 0 0 0 0 0), upper := (rows 769 7 52 88 250 234 234 234 490 746), lower := (rows 769 7 52 88 16 32 64 128 256 512), losses := [] }

theorem upper_31 : Upper D R [768,5,48,80] 13 :=
  bound_sound D R [768,5,48,80] 13 bound_31
    ((Boolean.boundCheck_true D R [768,5,48,80] 13 bound_31).mp (by decide +kernel))

def bound_32 : Bound 10 := { allowed := (rows 240 240 192 48 0 0 0 0 0 0), upper := (rows 769 7 52 200 250 250 250 250 506 762), lower := (rows 769 7 52 200 16 32 64 128 256 512), losses := [] }

theorem upper_32 : Upper D R [768,5,48,192] 13 :=
  bound_sound D R [768,5,48,192] 13 bound_32
    ((Boolean.boundCheck_true D R [768,5,48,192] 13 bound_32).mp (by decide +kernel))

def route_27 : Route 10 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_27 : Upper D R [768,5,48] 13 := by
  apply routed_branch D R [768,5,48] 13 (by decide) (choices 2) [18,48,66,80,192] route_27
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [768,5,48] (choices 2) [18,48,66,80,192] route_27).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact upper_28
  · exact upper_29
  · exact upper_30
  · exact upper_31
  · exact upper_32

def route_0 : Route 10 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 130 => (18,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 136 => (24,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [768,5] 13 := by
  apply routed_branch D R [768,5] 13 (by decide) (choices 2) [10,18,24,48] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [768,5] (choices 2) [10,18,24,48] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_11
  · exact upper_14
  · exact upper_27

theorem upper : Upper D R [768,5] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case55
