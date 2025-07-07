import Mathlib

#check YoungDiagram
#check SemistandardYoungTableau

structure YoungTableau (μ : YoungDiagram) where
  entry: μ.cells ≃ Fin μ.card

namespace YoungDiagram

def entry2fin (μ : YoungDiagram) (entry : μ.cells) : Fin μ.card := by
  rcases entry with ⟨⟨i, j⟩, hij⟩
  exact ⟨(List.take i μ.rowLens).sum + j, by sorry⟩

def fin2entry (μ : YoungDiagram) (a : Fin μ.card) : μ.cells :=
  sorry

def equivFin (μ : YoungDiagram) : μ.cells ≃ Fin μ.card :=
  { toFun := entry2fin μ
    invFun := fin2entry μ
    left_inv := sorry
    right_inv := sorry }

end YoungDiagram

namespace YoungTableau

variable {μ : YoungDiagram}

def whr (T : YoungTableau μ) (a : Fin μ.card) : μ.cells :=
  T.entry.invFun a

def mk_by_perm (perm : Equiv.Perm (Fin μ.card)) : YoungTableau μ :=
  { entry := Equiv.trans μ.equivFin perm}

instance : Inhabited (YoungTableau μ) where
  default := mk_by_perm default
@[simp] lemma default_def : (default : YoungTableau μ) = mk_by_perm default := by
  rfl

instance : FunLike (YoungTableau μ) μ (Fin μ.card) where
  coe := fun T => T.entry.toFun
  coe_injective' := by
    intros T₁ T₂ h
    cases T₁
    cases T₂
    simp at h
    rw [h]

abbrev 𝓢 (n : ℕ) := Equiv.Perm (Fin n)

instance permAction : MulAction (𝓢 μ.card) (YoungTableau μ) where
  smul g T := { entry := Equiv.trans T.entry g }
  one_smul := by intros; rfl
  mul_smul := by intros; rfl
lemma permAction_def (g : 𝓢 μ.card) (T : YoungTableau μ) :
  g • T = { entry := Equiv.trans T.entry g } := by rfl

instance : FaithfulSMul (𝓢 μ.card) (YoungTableau μ) where
  eq_of_smul_eq_smul := by
    rintro g₁ g₂ h
    ext a
    simp [permAction_def] at *
    specialize h (default : YoungTableau μ)
    simp at *
    rw [mk_by_perm] at h
    simp at h
    sorry

private def row_perms_finset (T : YoungTableau μ) : Finset (𝓢 μ.card) :=
  { p | ∀ (entry : μ.cells), (whr T ((p • T) entry)).1.fst = entry.1.fst }
def row_perms (T : YoungTableau μ): Subgroup (𝓢 μ.card) := {
  carrier := row_perms_finset T,
  one_mem' := by sorry
  mul_mem' := by sorry
  inv_mem' := by sorry
}
abbrev P (T : YoungTableau μ) := row_perms T

instance (T : YoungTableau μ) : Fintype (P T) := by
  apply Fintype.ofFinset (row_perms_finset T)
  intro p
  rfl

theorem P_conj (T : YoungTableau μ) (g : 𝓢 μ.card) : P (g • T) = {g * p' * g⁻¹ | p' ∈ P T} := by
  ext p
  sorry

private def col_perms_finset (T : YoungTableau μ) : Finset (𝓢 μ.card) :=
  { q | ∀ (entry : μ.cells), (whr T ((q • T) entry)).1.snd = entry.1.snd }
def col_perms (T : YoungTableau μ): Subgroup (𝓢 μ.card) := {
  carrier := col_perms_finset T,
  one_mem' := by sorry
  mul_mem' := by sorry
  inv_mem' := by sorry
}
abbrev Q (T : YoungTableau μ) := col_perms T

instance (T : YoungTableau μ) : Fintype (Q T) := by
  apply Fintype.ofFinset (col_perms_finset T)
  intro q
  rfl

theorem Q_conj (T : YoungTableau μ) (g : 𝓢 μ.card) : Q (g • T) = {g * p' * g⁻¹ | p' ∈ Q T} := by
  ext p
  sorry

end YoungTableau
