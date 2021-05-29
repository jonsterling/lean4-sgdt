import sgdt.later
import sgdt.domain

def lift (A : Type u) : Type u :=
fix R =>
Sum A ([▷] R)

macro "[" a:term "]⊥" : term =>
`(lift $a:term)

namespace lift
  def now (x : a) : [a]⊥ :=
  ltr.fix.intro $ Sum.inl x

  def step (x : ▷ [a]⊥) : [a]⊥ :=
  ltr.fix.intro $ Sum.inr $ by
  rw [dltr.red]
  exact x

  noncomputable def run [domain a] : [a]⊥ → a :=
  fix recbind => fun m =>
  match ltr.fix.elim m with
  | Sum.inl x => x
  | Sum.inr n =>
    domain.step $
    recbind ⊛ by simp at n; exact n
end lift

instance : domain [a]⊥ where
  step := lift.step

instance : Pure lift where
  pure := lift.now

noncomputable instance : Functor lift where
  map f :=
  fix recmap => fun m =>
  match ltr.fix.elim m with
  | Sum.inl x => pure $ f x
  | Sum.inr n =>
    domain.step $
    recmap ⊛ by simp at n; exact n

noncomputable instance : Bind lift where
  bind m k := lift.run $ k <$> m


namespace lift
  -- bind using the ▷-algebra structure of a domain
  noncomputable def dombind [domain b] (f : a → b) : [a]⊥ → b :=
  fix recbind => fun m => by
  match ltr.fix.elim m with
  | Sum.inl x =>
    exact f x
  | Sum.inr m' =>
    apply domain.step
    exact recbind ⊛ by
      simp at m'
      exact m'

  @[simp] constant dombind.now.red [domain b]  (f : a → b) (x : a) : dombind f (pure x) = f x := by
  simp [dombind, pure, now]
  rw [ltr.fix.red]
  simp

  @[simp] noncomputable constant dombind.step.red [domain b] (f : a -> b) (x : _) : dombind f (domain.step x) = domain.step (pure (dombind f) ⊛ x) :=
  fix rec => by
  simp [dombind,domain.step,step,pure]
  rw [ltr.fix.red]
  simp [domain.step]
  exact Eq.trans (by rw [ltr.fix.red]) (by simp)
end lift
