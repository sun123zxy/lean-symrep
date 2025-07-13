import Mathlib

#check YoungDiagram
#check SemistandardYoungTableau

namespace YoungDiagram

def entry2fin (μ : YoungDiagram) (entry : μ.cells) : Fin μ.card := by
  rcases entry with ⟨⟨i, j⟩, hij⟩
  exact ⟨(List.take i μ.rowLens).sum + j, by
    #check rowLen_eq_card
    #check Finset.card_union_of_disjoint
    #check mk_mem_row_iff

    have j_le_rowlen_i : j < μ.rowLen i := by
      change (i, j) ∈ μ at hij
      rw [mem_iff_lt_rowLen] at hij
      exact hij

    have i_lt_row_len : i < μ.rowLens.length := by
      simp only [length_rowLens]
      change (i, j) ∈ μ at hij
      rw [mem_iff_lt_colLen] at hij
      grw [μ.colLen_anti 0 j (show 0 ≤ j by linarith)] at hij
      assumption

    exact calc
      (List.take i μ.rowLens).sum + j < (List.take i μ.rowLens).sum + μ.rowLen i :=by
        linarith [j_le_rowlen_i]
      _ = (List.take (i+1) μ.rowLens).sum := by
        induction' i with i ih
        · simp
          rw [List.take_one]
          -- rcases μ.rowLens with _ | r
          -- · simp
          -- rw [List.sum_cons]
          sorry
        ·
          sorry
        -- rcases μ.rowLens with _ | r
        -- · simp

        --   sorry
        -- · simp

        --   sorry
        -- match i + 1, μ.rowLens with
        -- | 0, x => simp;
        -- | n+1, [] => simp;
        -- | n+1, a :: as => simp;
        -- rw [List.take_succ]
        -- simp
        -- rw [show μ.rowLen i = μ.rowLens[i] by simp]
        -- #check List.get?
        -- #check List.get_eq_getElem?

        -- rw [←List.get_eq_getElem?]

        -- cases μ.rowLens[i]? with
        -- | none =>
        --   simp

        -- | some r =>
        --   simp

        --   #check show μ.rowLens[i]? = r by sorry
        --

      _ ≤ μ.rowLens.sum := by

        sorry
      _ = μ.card := by
        rw [YoungDiagram.rowLens]
        rw [←YoungDiagram.length_rowLens]
        have : μ.rowLen = fun i => (μ.row i).card := by
          funext i
          rw [YoungDiagram.rowLen_eq_card]
        rw [this]

        sorry
  ⟩

def fin2entry (μ : YoungDiagram) (a : Fin μ.card) : μ.cells :=
  sorry

def equivFin (μ : YoungDiagram) : μ.cells ≃ Fin μ.card :=
  { toFun := entry2fin μ
    invFun := fin2entry μ
    left_inv := sorry
    right_inv := sorry }

end YoungDiagram

@[ext]
structure YoungTableau (μ : YoungDiagram) where
  entry: μ.cells ≃ Fin μ.card

namespace YoungTableau

variable {μ : YoungDiagram}

-- instance : EquivLike (YoungTableau μ) μ (Fin μ.card) where
--   coe T := T.entry.toFun
--   inv T := T.entry.invFun
--   left_inv := by intro T a; simp
--   right_inv := by intro T a; simp
--   coe_injective' := by
--     intros T₁ T₂ h
--     cases T₁
--     cases T₂
--     simp at h
--     rw [h]
--     simp

def mk_by_perm (perm : Equiv.Perm (Fin μ.card)) : YoungTableau μ :=
  ⟨Equiv.trans μ.equivFin perm⟩

instance : Inhabited (YoungTableau μ) where
  default := mk_by_perm default
@[simp] lemma default_def : (default : YoungTableau μ) = mk_by_perm default := by
  rfl

private abbrev 𝓢 (n : ℕ) := Equiv.Perm (Fin n)

instance permAction : MulAction (𝓢 μ.card) (YoungTableau μ) where
  smul g T := { entry := Equiv.trans T.entry g }
  one_smul := by intros; rfl
  mul_smul := by intros; rfl
lemma permAction_def (g : 𝓢 μ.card) (T : YoungTableau μ) :
  g • T = { entry := Equiv.trans T.entry g } := by rfl

def entry_perm_of_action (T : YoungTableau μ) (g : 𝓢 μ.card) : Equiv.Perm μ.cells :=
  (g • T).entry.trans T.entry.symm

instance : FaithfulSMul (𝓢 μ.card) (YoungTableau μ) where
  eq_of_smul_eq_smul := by
    rintro g₁ g₂ h
    simp [permAction_def] at *
    specialize h (default : YoungTableau μ)
    simp at *
    rw [mk_by_perm] at h
    simp at h
    apply_fun fun x => x.toFun at h
    simp at h
    apply_fun fun x => x ∘ ⇑μ.equivFin.symm at h
    repeat rw [Function.comp_assoc] at h
    simp at h
    assumption

private def row_perms_finset (T : YoungTableau μ) : Finset (𝓢 μ.card) :=
  { p | ∀ (e : μ.cells), (T.entry_perm_of_action p e).val.fst = e.val.fst }
def row_perms (T : YoungTableau μ): Subgroup (𝓢 μ.card) := {
  carrier := row_perms_finset T,
  one_mem' := by
    rw [row_perms_finset]
    simp
    intros
    simp [entry_perm_of_action]
  mul_mem' := by
    intro g₁ g₂ hg₁ hg₂
    rw [row_perms_finset] at *
    simp at *
    intro i j hij
    specialize hg₂ i j hij
    -- let ⟨⟨i', j'⟩, hij'⟩ : μ.cells := T.whr (g₂ (T.entry ⟨(i, j), hij⟩))
    let e' : μ.cells := T.entry_perm_of_action g₂ ⟨(i, j), hij⟩
    specialize hg₁ e'.val.fst e'.val.snd e'.property
    conv at hg₂ => lhs; congr; congr; change e'
    conv at hg₁ => rhs; rw [hg₂]
    conv => rhs; rw [←hg₁]
    unfold e'
    simp [entry_perm_of_action, permAction_def]
  inv_mem' := by
    intro g hg
    rw [row_perms_finset] at *
    simp at *
    intro i j hij
    let e' : μ.cells := T.entry_perm_of_action g ⟨(i, j), hij⟩
    rw [Equiv.Perm.inv_def]
    rw [entry_perm_of_action, permAction_def]
    simp

    sorry
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
  { q | ∀ (e : μ.cells), (T.entry.symm ((q • T).entry e)).val.snd = e.val.snd }
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
