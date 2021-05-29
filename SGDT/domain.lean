import sgdt.later

universe u

class domain (A : Type u) where
step : ▷ A → A

noncomputable def domain.fix [domain a] (f : a -> a) : a :=
fix x => f $ domain.step x

def is_strict [domain a] [domain b] (f : a -> b) :=
∀ x : ▷ a, f (domain.step x) = domain.step (f <$> x)

def strict_hom (a b : Type u) [domain a] [domain b] :=
{f : a → b // is_strict f}

infixr:50 "⊸" => strict_hom

instance [domain a] [domain b] : CoeFun (a ⊸ b) (fun _ => a → b) where
  coe f := f.val

noncomputable def bot [domain a] : a :=
fix x =>
domain.step x

notation "⊥" => bot

def strict_preserves_bot [domain a] [domain b] (f : a ⊸ b) : f ⊥ = ⊥ :=
  fix rec => by
  rw [ltr.lex] at rec
  simp [bot]
  rw [ltr.fix.red,f.property]
  simp [bot] at rec
  simp [Functor.map]
  rw [rec]
  apply Eq.symm
  exact Eq.trans (by rw [ltr.fix.red]) (by simp)

noncomputable instance {a b : Type u} [domain a] [domain b] : domain (a × b) where
  step :=
  fun p =>
  ⟨domain.step $ (fun x => x.1) <$> p,
   domain.step $ (fun x => x.2) <$> p⟩

noncomputable instance [domain b] : domain (a → b) where
  step :=
  fun f x =>
  domain.step $
  f ⊛ pure x