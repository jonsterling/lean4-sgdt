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

  @[simp] axiom seq.red : ∀ {f : (A → B)} {x : A}, next f ⊛ next x = next (f x)
end ltr

axiom dltr : ▷ Type u -> Type u
prefix:100 "[▷]" => dltr

@[simp] axiom dltr.red : {A : Type u} → [▷] next A = ▷ A

macro "fix " p:term " => " d:term : term =>
`(ltr.fix fun $p:term => $d:term)