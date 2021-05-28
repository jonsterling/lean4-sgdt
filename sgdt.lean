universe u

-- Currently needed until 'axiom' is fixed, see https://github.com/leanprover/lean4/issues/496
constant mysorry : ∀ {A}, A := sorry

constant ltr : Type u -> Type u := mysorry
prefix:100 "▷" => ltr

namespace ltr
  variable {A B : Type u}
  constant next : A → ▷ A := mysorry
  constant fix : (▷ A → A) → A := mysorry
  constant ap : ▷ (A → B) → ▷ A → ▷ B := mysorry
  infixl:100 "⊛" => ap

  @[simp] def Eq.mpr_mp_cancel : Eq.mpr (p : a = b) (Eq.mp (q : a = b) x) = x := by
  induction q
  simp [Eq.mpr,Eq.mp]

  namespace fix
    axiom red : {f : ▷ A → A} → fix f = f (next (fix f))

    variable {F : ▷ Type u → Type u}

    def intro : F (next (fix F)) → fix F := by
    intro x
    rw [← @red _ F] at x
    exact x

    def elim : fix F → F (next (fix F)) := by
    intro x
    rw [← @red _ F]
    exact x

    @[simp] def beta : (x : F (next (fix F))) → elim (intro x) = x := by
    intro x
    simp [intro,elim]

  end fix

  namespace ap
    axiom red : ∀ {f : (A → B)} {x : A}, (next f) ⊛ (next x) = next (f x)
  end ap
end ltr

axiom dltr : ▷ Type u -> Type u
prefix:100 "[▷]" => dltr

@[simp] axiom dltr.red : {A : Type u} → [▷] (ltr.next A) = ▷ A


class domain (A : Type u) where
step : ▷ A → A

inductive sum (A B : Type u) :=
| inl : A → sum A B
| inr : B → sum A B

def lift (A : Type u) : Type u :=
ltr.fix λ R =>
sum A ([▷] R)

namespace lift
  variable {A : Type u}

  def now (x : A) : lift A :=
  ltr.fix.intro $ sum.inl x

  def step (x : ▷ lift A) : lift A :=
  ltr.fix.intro $ sum.inr $ by
  rw [dltr.red]
  exact x

  instance : domain (lift A) where
    step := lift.step

  def bind [domain b] (f : A → b) : lift A → b := by
  apply @ltr.fix (lift A → b)
  intro recbind m
  match ltr.fix.elim m with
  | sum.inl x =>
    exact f x
  | sum.inr m' =>
    apply domain.step
    exact recbind ⊛ by
      simp at m'
      exact m'

  def bind.red [domain b]  (f : A → b) (x : A) : bind f (lift.now x) = f x := by
    simp [bind, now]
    rw [ltr.fix.red]
    simp

end lift

instance [domain a] [domain b] : domain (a × b) where
  step :=
  λ p =>
  ⟨domain.step (ltr.next (λ x => x.1) ⊛ p),
   domain.step (ltr.next (λ x => x.2) ⊛ p)⟩

instance [domain b] : domain (a → b) where
  step :=
  λ f x =>
  domain.step $
  f ⊛ ltr.next x