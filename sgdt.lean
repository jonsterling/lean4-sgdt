universe u


def from_singleton {P : Prop} : Subtype (fun x : Unit => P) → P := by
intro x
cases x
assumption

def to_singleton {P : Prop} : P → Subtype (fun x : Unit => P) := by
intro x
constructor
focus assumption
focus constructor


@[simp] constant Eq.mpr_mp_cancel : Eq.mpr (p : a = b) (Eq.mp (q : a = b) x) = x := by
induction q
simp [Eq.mpr,Eq.mp]


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
    @[simp] axiom red : ∀ {f : (A → B)} {x : A}, (next f) ⊛ (next x) = next (f x)
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

postfix:max "⊥" => lift

namespace lift
  def now (x : a) : a⊥ :=
  ltr.fix.intro $ sum.inl x

  def step (x : ▷ a⊥) : a⊥ :=
  ltr.fix.intro $ sum.inr $ by
  rw [dltr.red]
  exact x

  instance : domain a⊥ where
    step := lift.step

  def bind [domain b] (f : a → b) : a⊥ → b :=
  ltr.fix λ recbind => by
  intro m
  match ltr.fix.elim m with
  | sum.inl x =>
    exact f x
  | sum.inr m' =>
    apply domain.step
    exact recbind ⊛ by
      simp at m'
      exact m'

  constant bind.now.red [domain b]  (f : a → b) (x : a) : bind f (lift.now x) = f x := by
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

def domain.fix [domain a] (f : a -> a) : a :=
ltr.fix $ f ∘ domain.step
