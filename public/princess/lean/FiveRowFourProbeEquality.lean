import FiveRowFourProbeArithmetic

/-! Equality rigidity for the four-probe lower potential. -/
namespace Princess.FiveRowFourProbeArithmetic

set_option maxHeartbeats 2000000 in
theorem full_tight (h p b' z' : Nat) (hh : 15 ≤ h) (hmod : h%3=0)
    (hp : p≤4) (cap : b'≤h) (trans : Transition h h 0 p b' z')
    (tight : value h h 0 = p + value h b' z') :
    p=0 ∨ (p=2 ∧ b'=h-1 ∧ z'=0) := by
  rcases trans with ⟨hc,hb,hz⟩ | ⟨hc,hb,hnext,hz⟩ |
    ⟨hr,hcase,hmark,hb,hz⟩ | ⟨hr,hcap,hb,hz,hguard⟩ | ⟨hr,hb,hz⟩
  all_goals try (split at hz)
  all_goals subst_vars
  all_goals simp only [value,initial,last,core,hmod,Nat.reduceEqDiff,if_true,if_false] at tight
  all_goals
    try omega
    try (split at tight)
    all_goals try omega
    all_goals try (split at tight)
    all_goals try omega
    all_goals try (split at tight)
    all_goals try omega
    all_goals try (split at tight)
    all_goals try omega
    all_goals try (split at tight)
    all_goals try omega
    all_goals try (split at tight)
    all_goals try omega
    all_goals try (split at tight)
    all_goals first | omega | simp_all only [and_false]

set_option maxHeartbeats 2000000 in
theorem penultimate_tight (h p b' z' : Nat) (hh : 15 ≤ h) (hmod : h%3=0)
    (hp : p≤4) (cap : b'≤h) (trans : Transition h (h-1) 0 p b' z')
    (tight : value h (h-1) 0 = p + value h b' z') : p=4 := by
  rcases trans with ⟨hc,hb,hz⟩ | ⟨hc,hb,hnext,hz⟩ |
    ⟨hr,hcase,hmark,hb,hz⟩ | ⟨hr,hcap,hb,hz,hguard⟩ | ⟨hr,hb,hz⟩
  all_goals try (split at hz)
  all_goals subst_vars
  all_goals simp only [value,initial,last,core,hmod,Nat.reduceEqDiff,if_true,if_false] at tight
  all_goals
    try omega
    try (split at tight)
    all_goals try omega
    all_goals try (split at tight)
    all_goals try omega
    all_goals try (split at tight)
    all_goals try omega
    all_goals try (split at tight)
    all_goals try omega
    all_goals try (split at tight)
    all_goals try omega
    all_goals try (split at tight)
    all_goals try omega
    all_goals try (split at tight)
    all_goals first | omega | simp_all only [and_false]

end Princess.FiveRowFourProbeArithmetic
#print axioms Princess.FiveRowFourProbeArithmetic.full_tight
#print axioms Princess.FiveRowFourProbeArithmetic.penultimate_tight
