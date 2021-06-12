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


def Sp := [Unit]⊥
notation "Σ" => Sp

inductive Sp.approx_f (H : ▷ (Sp → Sp → Prop)) : Sp → Sp → Prop :=
| now : ∀ x y x' y', x' = lift.now x → y' = lift.now y → approx_f H x' y'
| step_now : ∀ x y x' y', x' = lift.step x → y' = lift.now y →  approx_f H x' y'
| step_step : ∀ x y x' y', x' = lift.step x → y' = lift.step y → [▷] (H ⊛ x ⊛ y) → approx_f H x' y'

noncomputable def Sp.approx : Sp → Sp → Prop :=
  fix H =>
  Sp.approx_f H

noncomputable def approx [domain a] : a → a → Prop :=
  fun x y =>
  ∀ φ : a → Σ,
  Sp.approx (φ x) (φ y)

infix:100 "⊑" => approx

def step_now_noconf : ∀ x (y : a), lift.step x = lift.now y → False := by
  intro x y P
  simp [lift.step, lift.now] at P
  have Q := congrArg ltr.fix.elim P
  simp at Q


def now_approx_step_false : ∀ (x : Unit) (y : ▷ Σ), Sp.approx (lift.now x) (lift.step y) → False := by
  intro x y
  simp [Sp.approx]
  rw [ltr.fix.red]
  intro H
  cases H with
  | now =>
    apply step_now_noconf
    assumption
  | step_now =>
    apply step_now_noconf
    assumption
  | step_step =>
    apply step_now_noconf
    apply Eq.symm
    assumption

def now_approx_inversion : Sp.approx (lift.now PUnit.unit) y → y = lift.now PUnit.unit := sorry

def abort : False → a := by
  intro x
  cases x

def sp_approx_f_trans : ∀ x y z, Sp.approx_f Sp.approx x y → Sp.approx_f Sp.approx y z → Sp.approx_f Sp.approx x z :=
  fix IH => by
  intro x y z xy yz
  cases xy with
  | now x' y' _ _ p q =>
    simp_all
  | step_now x' y' _ _ p q =>
    cases y'
    suffices h : z = lift.now PUnit.unit by
      apply Sp.approx_f.step_now <;> try assumption
    apply now_approx_inversion
    simp [Sp.approx]
    rw [ltr.fix.red]
    rw [q] at yz
    assumption
  | step_step x' y' h1 h2 px py x'y' =>
    cases yz with
    | now =>
      apply Sp.approx_f.step_now <;> assumption
    | step_now =>
      apply Sp.approx_f.step_now <;> assumption
    | step_step h1 h2 h3 h4 h5 h6 h7 =>
      apply Sp.approx_f.step_step <;> try assumption
      have IH' := forall_ltr2 IH x' h2
      exact sorry


def sp_approx_trans : ∀ x y z, Sp.approx x y → Sp.approx y z → Sp.approx x z := by
  intro x y z
  simp [Sp.approx]
  rw [ltr.fix.red]
  apply sp_approx_f_trans


def approx_trans [domain a] : ∀ x y z : a, x ⊑ y → y ⊑ z → x ⊑ z := by
  intro x y z xy yz φ
  let xyφ := xy φ
  let yzφ := yz φ
  apply sp_approx_trans <;> assumption