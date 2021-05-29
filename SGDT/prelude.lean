@[simp] constant Eq.mpr_mp_cancel : Eq.mpr (p : a = b) (Eq.mp (q : a = b) x) = x := by
induction q
simp [Eq.mpr,Eq.mp]

@[simp] constant Eq.mp_mpr_cancel : Eq.mp (p : a = b) (Eq.mpr (q : a = b) x) = x := by
induction q
simp [Eq.mpr,Eq.mp]