import FiniteSubsetProfiles

/-! A generic checker of all predecessor-closed subsets. Inclusion of a vertex
forces its entire supplied predecessor mask. Its soundness does not require
that a proposed enumeration is complete by assumption. -/
namespace Princess.FiniteIdealCertificates
open Princess.FiniteSubsetProfiles

def BitSubset (a b : Nat) : Prop := ∀ j, a.testBit j = true → b.testBit j = true

theorem bitSubset_antisymm {a b : Nat} (ab : BitSubset a b) (ba : BitSubset b a) : a=b := by
  apply Nat.eq_of_testBit_eq
  intro j
  have ha := ab j
  have hb := ba j
  cases h1 : a.testBit j <;> cases h2 : b.testBit j <;> simp_all

def check (down : Nat → Nat) (P : Nat → Bool) : List Nat → Nat → Bool
  | [], mask => P mask
  | v::vs, mask => if mask.testBit v then check down P vs mask
      else check down P vs mask && check down P vs (mask ||| down v)

theorem check_forced (down : Nat → Nat) (P : Nat → Bool) (v : Nat) (vs : List Nat) (mask : Nat)
    (forced : mask.testBit v=true) (tail : check down P vs mask=true) :
    check down P (v::vs) mask=true := by
  change (if mask.testBit v then check down P vs mask else
    check down P vs mask && check down P vs (mask ||| down v))=true
  rw [if_pos forced]
  exact tail

theorem check_branch (down : Nat → Nat) (P : Nat → Bool) (v : Nat) (vs : List Nat) (mask : Nat)
    (free : mask.testBit v=false) (absent : check down P vs mask=true)
    (present : check down P vs (mask ||| down v)=true) :
    check down P (v::vs) mask=true := by
  change (if mask.testBit v then check down P vs mask else
    check down P vs mask && check down P vs (mask ||| down v))=true
  rw [free]
  simpa only [Bool.false_eq_true,ite_false,Bool.and_eq_true] using And.intro absent present

theorem check_sound (down : Nat → Nat) (P : Nat → Bool) (vs : List Nat)
    (target mask : Nat) (included : BitSubset mask target)
    (covered : ∀ j, target.testBit j = true → mask.testBit j = true ∨ j ∈ vs)
    (self : ∀ v ∈ vs, (down v).testBit v = true)
    (closed : ∀ v ∈ vs, target.testBit v = true → BitSubset (down v) target)
    (checked : check down P vs mask = true) : P target = true := by
  induction vs generalizing mask with
  | nil =>
      have eq : mask = target := bitSubset_antisymm included (fun j hj => by
        rcases covered j hj with h | h
        · exact h
        · simp at h)
      simpa only [check,eq] using checked
  | cons v vs ih =>
      have selftail := fun u hu => self u (List.mem_cons_of_mem v hu)
      have closedtail := fun u hu => closed u (List.mem_cons_of_mem v hu)
      by_cases present : mask.testBit v = true
      · have hcheck : check down P vs mask = true := by simpa [check,present] using checked
        apply ih mask included _ selftail closedtail hcheck
        intro j hj
        rcases covered j hj with h | h
        · exact Or.inl h
        · rcases List.mem_cons.mp h with h | h
          · subst j; exact Or.inl present
          · exact Or.inr h
      · have both : check down P vs mask = true ∧ check down P vs (mask ||| down v) = true := by
          simpa [check,present] using checked
        by_cases wanted : target.testBit v = true
        · apply ih (mask ||| down v) _ _ selftail closedtail both.2
          · intro j hj
            rw [Nat.testBit_or,Bool.or_eq_true] at hj
            rcases hj with hj | hj
            · exact included j hj
            · exact closed v List.mem_cons_self wanted j hj
          · intro j hj
            rcases covered j hj with h | h
            · exact Or.inl (by simpa only [Nat.testBit_or,Bool.or_eq_true] using Or.inl h)
            · rcases List.mem_cons.mp h with h | h
              · subst j
                exact Or.inl (by simp only [Nat.testBit_or,self v List.mem_cons_self,Bool.or_true])
              · exact Or.inr h
        · apply ih mask included _ selftail closedtail both.1
          intro j hj
          rcases covered j hj with h | h
          · exact Or.inl h
          · rcases List.mem_cons.mp h with h | h
            · subst j; exact False.elim (wanted hj)
            · exact Or.inr h

end Princess.FiniteIdealCertificates
#print axioms Princess.FiniteIdealCertificates.check_sound
