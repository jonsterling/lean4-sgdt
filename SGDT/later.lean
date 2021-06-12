import sgdt.prelude

universes u v
axiom ltr : Sort u -> Sort u
prefix:100 "▷" => ltr

axiom next : {A : Sort u} → A → ▷ A

noncomputable instance : Pure ltr where
  pure := next

section
  variable {A : Sort u} {B : Sort v}
  axiom ltr.seq : ▷ (A → B) → ▷ A → ▷ B
  infixl:60 "⊛" => ltr.seq

  noncomputable instance : Seq ltr where
    seq := ltr.seq

  noncomputable instance : Functor ltr where
    map f x := next f ⊛ x
end


namespace ltr
  variable {A B : Sort u}
  axiom fix : (▷ A → A) → A
  axiom lex : ∀ x y : A, ▷ (x = y) = (next x = next y)

  namespace fix
    axiom red : {f : ▷ A → A} → fix f = f (next (fix f))

    variable {F : ▷ Sort u → Sort u}

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

  @[simp] axiom seq.red : ∀ {f : (A → B)} {x : A}, next f ⊛ next x = next (f x)
end ltr

class flasque (A : Type u) : Prop where
  next_surj : ∀ x : ▷ A, ∃ y : A, x = pure y

axiom exists_ltr {A : Type u} [flasque A] [Nonempty A] {P : A → Prop} : (▷ ∃ x : A, P x) → ∃ x : A, ▷ P x

axiom Nat_next_surj : ∀ x : ▷ Nat, ∃ y : Nat, x = pure y

instance : flasque Nat where
  next_surj := Nat_next_surj


axiom dltr : ▷ Sort u -> Sort u
prefix:100 "[▷]" => dltr

@[simp] axiom dltr.red : {A : Sort u} → [▷] next A = ▷ A

macro "fix " p:term " => " d:term : term =>
`(ltr.fix fun $p:term => $d:term)


axiom forall_ltr {A : Type u} {P : A → Prop} : (▷ ∀ x : A, P x) → ∀ x : ▷ A, [▷] (next P ⊛ x)
axiom forall_ltr2 {A : Type u} {P : A → A → Prop} : (▷ ∀ x y : A, P x y) → ∀ x y : ▷ A, [▷] (next P ⊛ x ⊛ y)