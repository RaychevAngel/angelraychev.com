import OddEndpointObjective111Transfer
import OddEndpointObjective111Delivery0
import OddEndpointObjective111Delivery1
import OddEndpointObjective111Delivery2
import OddEndpointObjective111Delivery3
import OddEndpointObjective111Delivery4
/- Translation of immutable odd-endpoint local strategies; see the export
manifest for exact archive and record pins. The exporter is untrusted.
All finite game and entry obligations below are checked by the Lean kernel. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.OddEndpointCertificate111
open LocalArena OddEndpointLocal OddEndpointCertificatesSpec GroupedArena
open OddEndpointPattern111
noncomputable def certificates : Certificates residue patchAnchor where
  transfer := OddEndpointObjective111Transfer.certificate
  delivery := by
    intro j allowed
    apply Classical.choice
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by
      have finite : ∀ j : Fin 6, j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by decide +kernel
      exact finite j
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨OddEndpointObjective111Delivery0.certificate⟩
    · exact ⟨OddEndpointObjective111Delivery1.certificate⟩
    · exact ⟨OddEndpointObjective111Delivery2.certificate⟩
    · exact ⟨OddEndpointObjective111Delivery3.certificate⟩
    · exact ⟨OddEndpointObjective111Delivery4.certificate⟩
    · exact False.elim ((by decide : ¬targetAllowed residue patchAnchor 5) allowed)
#print axioms certificates
end Delivery.OddEndpointCertificate111
