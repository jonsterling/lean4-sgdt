import sgdt.domain
import sgdt.lift

class storable (a : Type) [domain a] where
  store : [domain b] → (a → b) → (a ⊸ b)

noncomputable instance : storable [a]⊥ where
  store {b} _ f :=
  ⟨fun m => lift.dombind (f ∘ lift.now) m,
   fun _ => by simp [is_strict, Functor.map,pure]⟩