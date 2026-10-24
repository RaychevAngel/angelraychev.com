import SixTypeObjective07Transfer
import SixTypeObjective07Delivery0
import SixTypeObjective07Delivery1
import SixTypeObjective07Delivery2
import SixTypeObjective07Delivery3
import SixTypeObjective07Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate07
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern07.pattern := by
  constructor
  · exact ⟨SixTypeObjective07Transfer.data, SixTypeObjective07Transfer.checked, SixTypeObjective07Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective07Delivery0.data, SixTypeObjective07Delivery0.checked, SixTypeObjective07Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective07Delivery1.data, SixTypeObjective07Delivery1.checked, SixTypeObjective07Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective07Delivery2.data, SixTypeObjective07Delivery2.checked, SixTypeObjective07Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective07Delivery3.data, SixTypeObjective07Delivery3.checked, SixTypeObjective07Delivery3.initial_states⟩
    · simp [SixTypePattern07.pattern] at present
    · exact ⟨SixTypeObjective07Delivery5.data, SixTypeObjective07Delivery5.checked, SixTypeObjective07Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate07
