axiom F : Type
constant foo : F := sorry
def foo' : F := foo


--instance [domain a] [domain b] : domain (a × b) where
--  step :=
--  λ p =>
--  ⟨domain.step ((ltr.next (λ x => x.1)) ⊛ p),
--   domain.step ((ltr.next (λ x => x.2)) ⊛ p)⟩