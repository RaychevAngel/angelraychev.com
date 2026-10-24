import FiveShortTransfer
import FiveShortDelivery0
import FiveShortDelivery1
import FiveShortDelivery2
import FiveShortDelivery3
import FiveShortDelivery4
namespace Delivery.FiveShortCertificates
open FiveTypeWindow FiveShortArena
noncomputable def delivery (t : Fin 5) : LocalArena.Data R C :=
  if t=0 then FiveShortDelivery0.data else if t=1 then FiveShortDelivery1.data else
  if t=2 then FiveShortDelivery2.data else if t=3 then FiveShortDelivery3.data else FiveShortDelivery4.data
noncomputable def certificates : Certificates arena 26 where
  transfer := FiveShortTransfer.data
  transfer_checked := FiveShortTransfer.checked
  transfer_entries := FiveShortTransfer.entries
  delivery := delivery
  delivery_checked := by
    intro t
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
    rcases cases with rfl|rfl|rfl|rfl|rfl
    · simpa [delivery] using FiveShortDelivery0.checked
    · simpa [delivery] using FiveShortDelivery1.checked
    · simpa [delivery] using FiveShortDelivery2.checked
    · simpa [delivery] using FiveShortDelivery3.checked
    · simpa [delivery] using FiveShortDelivery4.checked
  delivery_entries := by
    intro t r c entry safe
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
    rcases cases with rfl|rfl|rfl|rfl|rfl
    · have result := FiveShortDelivery0.entries r c entry safe
      exact ⟨by simpa [delivery] using result.1,by simpa [delivery] using (Nat.le_trans result.2 (by decide : 26≤26))⟩
    · have result := FiveShortDelivery1.entries r c entry safe
      exact ⟨by simpa [delivery] using result.1,by simpa [delivery] using (Nat.le_trans result.2 (by decide : 19≤26))⟩
    · have result := FiveShortDelivery2.entries r c entry safe
      exact ⟨by simpa [delivery] using result.1,by simpa [delivery] using (Nat.le_trans result.2 (by decide : 17≤26))⟩
    · have result := FiveShortDelivery3.entries r c entry safe
      exact ⟨by simpa [delivery] using result.1,by simpa [delivery] using (Nat.le_trans result.2 (by decide : 17≤26))⟩
    · have result := FiveShortDelivery4.entries r c entry safe
      exact ⟨by simpa [delivery] using result.1,by simpa [delivery] using (Nat.le_trans result.2 (by decide : 18≤26))⟩

#print axioms certificates
end Delivery.FiveShortCertificates
