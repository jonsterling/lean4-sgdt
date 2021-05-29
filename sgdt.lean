universe u

@[simp] constant Eq.mpr_mp_cancel : Eq.mpr (p : a = b) (Eq.mp (q : a = b) x) = x := by
induction q
simp [Eq.mpr,Eq.mp]

@[simp] constant Eq.mp_mpr_cancel : Eq.mp (p : a = b) (Eq.mpr (q : a = b) x) = x := by
induction q
simp [Eq.mpr,Eq.mp]

inductive sum (A B : Type u) :=
| inl : A → sum A B
| inr : B → sum A B

axiom ltr : Sort u -> Sort u
prefix:100 "▷" => ltr

namespace ltr
  variable {A B : Sort u}
  axiom next : A → ▷ A
  axiom fix : (▷ A → A) → A
  axiom ap : ▷ (A → B) → ▷ A → ▷ B
  infixl:100 "⊛" => ap

  axiom lex : ∀ x y : A, ▷ (x = y) = (next x = next y)

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

    @[simp] def beta (x : F (next (fix F))) : elim (intro x) = x := by
    simp [intro,elim]

    @[simp] def eta (x : fix F) : intro (elim x) = x := by
    simp [intro,elim]
  end fix

  @[simp] axiom ap.red : ∀ {f : (A → B)} {x : A}, (next f) ⊛ (next x) = next (f x)
end ltr

axiom dltr : ▷ Type u -> Type u
prefix:100 "[▷]" => dltr

@[simp] axiom dltr.red : {A : Type u} → [▷] ltr.next A = ▷ A


class domain (A : Type u) where
step : ▷ A → A


macro "fix " p:term " => " d:term : term =>
`(ltr.fix fun $p:term => $d:term)

def is_strict [domain a] [domain b] (f : a -> b) :=
∀ x : ▷ a, f (domain.step x) = domain.step (ltr.next f ⊛ x)

def strict_hom (a b : Type u) [domain a] [domain b] :=
{f : a → b // is_strict f}

infixr:50 "⊸" => strict_hom

instance [domain a] [domain b] : CoeFun (strict_hom a b) (fun _ => a → b) where
  coe f := f.val


def lift (A : Type u) : Type u :=
fix R =>
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

  noncomputable def bind [domain b] (f : a → b) : a⊥ → b :=
  fix recbind => fun m => by
  match ltr.fix.elim m with
  | sum.inl x =>
    exact f x
  | sum.inr m' =>
    apply domain.step
    exact recbind ⊛ by
      simp at m'
      exact m'

  macro x:term "←" m:term "in" n:term : term =>
    `(bind (fun $x:term => $n:term) $m:term)

  @[simp] constant bind.now.red [domain b]  (f : a → b) (x : a) : bind f (lift.now x) = f x := by
  simp [bind, now]
  rw [ltr.fix.red]
  simp

  @[simp] constant bind.step.red [domain b] (f : a -> b) (x : _) : bind f (domain.step x) = domain.step (ltr.next (bind f) ⊛ x) :=
  fix rec => by
  simp [bind,domain.step,step]
  rw [ltr.fix.red]
  simp [domain.step]
  exact Eq.trans (by rw [ltr.fix.red]) (by simp)

end lift


class storable (a : Type) [domain a] where
  store : [domain b] → (a → b) → (a ⊸ b)

noncomputable instance : storable a⊥ where
  store {b} _ f :=
  ⟨fun m => x ← m in f $ lift.now x,
   fun _ => by simp [is_strict]⟩

noncomputable instance {a b : Type u} [domain a] [domain b] : domain (a × b) where
  step :=
  fun p =>
  ⟨domain.step $ ltr.next (fun x => x.1) ⊛ p,
   domain.step $ ltr.next (fun x => x.2) ⊛ p⟩

noncomputable instance [domain b] : domain (a → b) where
  step :=
  fun f x =>
  domain.step $
  f ⊛ ltr.next x

noncomputable def domain.fix [domain a] (f : a -> a) : a :=
fix x => f $ domain.step x


noncomputable def bot [domain a] : a :=
fix x =>
domain.step x

def strict_preserves_bot [domain a] [domain b] (f : a ⊸ b) : f bot = bot :=
  fix rec => by
  rw [ltr.lex] at rec
  simp [bot]
  rw [ltr.fix.red,f.property,ltr.ap.red]
  simp [bot] at rec
  rw [rec]
  apply Eq.symm
  exact Eq.trans (by rw [ltr.fix.red]) (by simp)