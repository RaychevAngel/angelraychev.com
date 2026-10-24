import OddEndpointPattern048
/- Translation of immutable odd-endpoint local strategies; see the export
manifest for exact archive and record pins. The exporter is untrusted.
All finite game and entry obligations below are checked by the Lean kernel. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.OddEndpointObjective048Transfer
open LocalArena OddEndpointLocal OddEndpointCertificatesSpec GroupedArena
open OddEndpointPattern048
noncomputable def groupRows (r : Nat) : List (Group 66 91) := (if r < 33 then (if r < 16 then (if r < 8 then (if r < 4 then (if r < 2 then (if r < 1 then [] else []) else (if r < 3 then [] else [])) else (if r < 6 then (if r < 5 then [] else []) else (if r < 7 then [] else []))) else (if r < 12 then (if r < 10 then (if r < 9 then [] else []) else (if r < 11 then [] else [])) else (if r < 14 then (if r < 13 then [] else []) else (if r < 15 then [] else [])))) else (if r < 24 then (if r < 20 then (if r < 18 then (if r < 17 then [] else []) else (if r < 19 then [] else [])) else (if r < 22 then (if r < 21 then [] else []) else (if r < 23 then [] else []))) else (if r < 28 then (if r < 26 then (if r < 25 then [] else []) else (if r < 27 then [] else [])) else (if r < 30 then (if r < 29 then [] else []) else (if r < 31 then [{rank:=0,move:=30,cops:=[6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,43,44,45,46,47,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,90],mask:=1257282852398365518717779904}] else (if r < 32 then [] else [{rank:=0,move:=32,cops:=[6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,45,46,47,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,90],mask:=1257282852398352324578246592}])))))) else (if r < 49 then (if r < 41 then (if r < 37 then (if r < 35 then (if r < 34 then [{rank:=0,move:=33,cops:=[32,33,36,37,39,40,42,43,44,46,50,51,52,53,54,55],mask:=71034717511614464}] else [{rank:=0,move:=34,cops:=[6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,47,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,90],mask:=1257282852398299548020113344}]) else (if r < 36 then [] else [])) else (if r < 39 then (if r < 38 then [] else [{rank:=1,move:=30,cops:=[6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,43,44,45,46,47,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,90],mask:=1257282852397237419787681728},{rank:=2,move:=39,cops:=[41],mask:=2199023255552},{rank:=3,move:=39,cops:=[42],mask:=4398046511104}]) else (if r < 40 then [{rank:=1,move:=32,cops:=[6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,45,46,47,50,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,90],mask:=1257282852396091728671539136},{rank:=2,move:=40,cops:=[43],mask:=8796093022208},{rank:=6,move:=40,cops:=[44],mask:=17592186044416}] else [{rank:=1,move:=34,cops:=[6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,47,50,51,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,90],mask:=1257282852393760764020654016},{rank:=5,move:=41,cops:=[45],mask:=35184372088832},{rank:=7,move:=41,cops:=[46],mask:=70368744177664}]))) else (if r < 45 then (if r < 43 then (if r < 42 then [{rank:=3,move:=42,cops:=[38,40,45],mask:=36558761623552},{rank:=4,move:=42,cops:=[46],mask:=70368744177664},{rank:=6,move:=42,cops:=[47],mask:=140737488355328}] else [{rank:=2,move:=39,cops:=[30,34,38,39,40,41,45,46],mask:=109694538481664},{rank:=3,move:=39,cops:=[47],mask:=140737488355328},{rank:=5,move:=43,cops:=[43,50],mask:=1134695999864832}]) else (if r < 44 then [{rank:=2,move:=44,cops:=[42,50,53],mask:=10137497208094720},{rank:=4,move:=44,cops:=[43,44,51],mask:=2278188092751872}] else [{rank:=1,move:=33,cops:=[36,39,42,43,50,51,52,53,54],mask:=34916709726945280},{rank:=3,move:=45,cops:=[44,45],mask:=52776558133248}])) else (if r < 47 then (if r < 46 then [{rank:=2,move:=38,cops:=[36,38,44,45,46],mask:=123488899694592}] else []) else (if r < 48 then [] else [])))) else (if r < 57 then (if r < 53 then (if r < 51 then (if r < 50 then [] else []) else (if r < 52 then [] else [])) else (if r < 55 then (if r < 54 then [] else []) else (if r < 56 then [] else []))) else (if r < 61 then (if r < 59 then (if r < 58 then [] else []) else (if r < 60 then [] else [])) else (if r < 63 then (if r < 62 then [] else []) else (if r < 64 then [] else (if r < 65 then [] else [])))))))
noncomputable def rows (x : R) : List (Group 66 91) := groupRows x.val
noncomputable def data : LocalArena.Data R C := GroupedArena.data rows
theorem groups_checked : Checked false frozenArena (safeGoal residue patchAnchor) replyMasks collisionMasks rows := by
  unfold Checked
  decide +kernel
theorem checked : SafeChecked (arena residue patchAnchor) (safeGoal residue patchAnchor) data := by
  rw [←arena_eq]
  exact GroupedArena.safe_checked frozenArena (safeGoal residue patchAnchor) replyMasks collisionMasks rows
    reply_coverage collision_coverage groups_checked
def entryBits (r : Nat) : Nat := (if r < 33 then (if r < 16 then (if r < 8 then (if r < 4 then (if r < 2 then (if r < 1 then 0 else 0) else (if r < 3 then 0 else 0)) else (if r < 6 then (if r < 5 then 0 else 0) else (if r < 7 then 0 else 0))) else (if r < 12 then (if r < 10 then (if r < 9 then 0 else 0) else (if r < 11 then 0 else 0)) else (if r < 14 then (if r < 13 then 0 else 0) else (if r < 15 then 0 else 0)))) else (if r < 24 then (if r < 20 then (if r < 18 then (if r < 17 then 0 else 0) else (if r < 19 then 0 else 0)) else (if r < 22 then (if r < 21 then 0 else 0) else (if r < 23 then 0 else 0))) else (if r < 28 then (if r < 26 then (if r < 25 then 0 else 0) else (if r < 27 then 0 else 0)) else (if r < 30 then (if r < 29 then 0 else 0) else (if r < 31 then 1257282852398365518717779904 else (if r < 32 then 0 else 1257282852398352324578246592)))))) else (if r < 49 then (if r < 41 then (if r < 37 then (if r < 35 then (if r < 34 then 71034717511614464 else 1257282852398299548020113344) else (if r < 36 then 0 else 0)) else (if r < 39 then (if r < 38 then 0 else 1257282852397244016857448384) else (if r < 40 then 1257282852396118116950605760 else 1257282852393866317136920512))) else (if r < 45 then (if r < 43 then (if r < 42 then 247664994156544 else 1385128026701824) else (if r < 44 then 12415685300846592 else 34969486285078528)) else (if r < 47 then (if r < 46 then 123488899694592 else 0) else (if r < 48 then 0 else 0)))) else (if r < 57 then (if r < 53 then (if r < 51 then (if r < 50 then 0 else 0) else (if r < 52 then 0 else 0)) else (if r < 55 then (if r < 54 then 0 else 0) else (if r < 56 then 0 else 0))) else (if r < 61 then (if r < 59 then (if r < 58 then 0 else 0) else (if r < 60 then 0 else 0)) else (if r < 63 then (if r < 62 then 0 else 0) else (if r < 64 then 0 else (if r < 65 then 0 else 0)))))))
def boundedMasks (x : R) : Nat := entryBits x.val
def originalBound : Nat := 7
theorem bounded_agrees : ∀ x, lowerMask (rows x) (originalBound+1)=boundedMasks x := by
  decide +kernel
theorem entry_subset : ∀ x, transferEntry residue patchAnchor x →
    requiredMasks x &&& boundedMasks x=requiredMasks x := by
  decide +kernel
theorem initial_states : ∀ x c, transferEntry residue patchAnchor x → presentC residue patchAnchor c →
    ¬(arena residue patchAnchor).collision x c →
    data.region x c ∧ data.rank x c≤originalBound := by
  intro x c entry pc safe
  apply GroupedArena.bounded rows x c originalBound
  rw [bounded_agrees]
  exact has_subset (entry_subset x entry) (required_coverage x c entry.1 pc safe)
noncomputable def certificate : Transfer residue patchAnchor where
  data := data
  checked := checked
  starts := by
    intro x c entry pc safe
    obtain ⟨inside,bound⟩ := initial_states x c entry pc safe
    exact ⟨inside,Nat.le_trans bound (by decide : originalBound≤transferBound residue)⟩
#print axioms certificate
end Delivery.OddEndpointObjective048Transfer
