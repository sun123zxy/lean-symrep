import Mathlib
import Symrep.YoungTableau

#check MonoidAlgebra.singleOneAlgHom
#check MonoidAlgebra.of

noncomputable instance (G : Type) (k : Type) [Monoid G] [Field k] :
    Coe G (MonoidAlgebra k G) where
  coe := MonoidAlgebra.of k G

abbrev 𝓢 (n : ℕ) := Equiv.Perm (Fin n)

def tp {n : ℕ} (i j : Fin n) : 𝓢 n :=
  let f := fun a => if a = i then j else if a = j then i else a
  ⟨ f, f, by intro a; aesop, by intro a; aesop⟩

variable {μ : YoungDiagram}

theorem SRDC_iff (T : YoungTableau μ) (g : 𝓢 μ.card) :
      (∀ i j : Fin μ.card, i ≠ j → tp i j ∈ T.P → tp i j ∉ T.Q)
    ↔ (∃ p ∈ T.P, ∃ q ∈ T.Q, g = p * q) := by
  sorry

section

variable (k : Type) [Field k]

noncomputable def RowSymmetrizer (T : YoungTableau μ) : MonoidAlgebra k (𝓢 μ.card) :=
  ∑ p : T.P, p
noncomputable abbrev α (T : YoungTableau μ) := RowSymmetrizer k T
lemma RowSymmetrizer_def (T : YoungTableau μ) :
    α k T = ∑ p : T.P, (p : MonoidAlgebra k (𝓢 μ.card)) := by
  rfl

-- lemma temp (G : Type) [Group G] (h : G) : (Set.univ : Set G) = {h * g | g : G} := by

@[simp] lemma pa_eq (T : YoungTableau μ) (p : T.P) :
    p * (α k T) = α k T := by
    rw [RowSymmetrizer_def]
    rw [Finset.mul_sum]
    simp
    apply Fintype.sum_equiv (Equiv.mulLeft p)
    intro x
    simp

@[simp] lemma ap_eq (T : YoungTableau μ) (p : T.P) :
    (α k T) * p = α k T := by
    rw [RowSymmetrizer_def]
    rw [Finset.sum_mul]
    simp
    apply Fintype.sum_equiv (Equiv.mulRight p)
    intro x
    simp

noncomputable def ColumnSymmetrizer (T : YoungTableau μ) : MonoidAlgebra k (𝓢 μ.card) :=
  ∑ q : T.Q, ((q : 𝓢 μ.card).sign : k) • q
noncomputable abbrev β (T : YoungTableau μ) := ColumnSymmetrizer k T
lemma ColumnSymmetrizer_def (T : YoungTableau μ) :
    β k T = ∑ q : T.Q, ((q : 𝓢 μ.card).sign : k) • (q : MonoidAlgebra k (𝓢 μ.card)) := by
  rfl

noncomputable def YoungSymmetrizer (T : YoungTableau μ) : MonoidAlgebra k (𝓢 μ.card) :=
  α k T * β k T
noncomputable abbrev γ (T : YoungTableau μ) := YoungSymmetrizer k T
lemma γ_def (T : YoungTableau μ) : γ k T = α k T * β k T := by
  rfl

@[simp] lemma qb_eq (T : YoungTableau μ) (q : T.Q) :
    q * (β k T) = ((q : 𝓢 μ.card).sign : k) • β k T := by
  rw [ColumnSymmetrizer_def]
  rw [Finset.mul_sum, Finset.smul_sum]
  simp only [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single, smul_eq_mul, mul_one,
    MonoidAlgebra.single_mul_single, one_mul]
  apply Fintype.sum_equiv (Equiv.mulLeft q)
  intro x
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]
  ring_nf
  have h : ((q : 𝓢 μ.card).sign : k)^2 = 1 := by
    simp
    have h' := Int.units_eq_one_or (q : 𝓢 μ.card).sign
    aesop
  rw [h]
  simp

@[simp] lemma bq_eq (T : YoungTableau μ) (q : T.Q) :
    (β k T) * q = ((q : 𝓢 μ.card).sign : k) • β k T := by
  rw [ColumnSymmetrizer_def]
  rw [Finset.sum_mul, Finset.smul_sum]
  simp only [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single, smul_eq_mul, mul_one,
    MonoidAlgebra.single_mul_single, mul_one]
  apply Fintype.sum_equiv (Equiv.mulRight q)
  intro x
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]
  ring_nf
  have h : ((q : 𝓢 μ.card).sign : k)^2 = 1 := by
    simp
    have h' := Int.units_eq_one_or (q : 𝓢 μ.card).sign
    aesop
  rw [h]
  simp

theorem young_symmetrizer_iff (T : YoungTableau μ) (γ' : MonoidAlgebra k (𝓢 μ.card)) :
    (∀ p : T.P, ∀ q : T.Q, p * γ' * q = ((q : 𝓢 μ.card).sign : k) • γ')
    ↔ (∃ c : k, γ' = c • (γ k T)) := by
  sorry

lemma cxc (T : YoungTableau μ) (x : MonoidAlgebra k (𝓢 μ.card)) :
  ∃ c : k, (γ k T) * x * (γ k T) = ↑c • (γ k T) := by
  have h := (young_symmetrizer_iff k T ((γ k T) * x * (γ k T))).mp
  apply h
  intro p q
  rw [γ_def]
  repeat rw [←mul_assoc]
  rw [pa_eq]
  repeat rw [mul_assoc]
  rw [bq_eq]
  simp

def SpechtModule (T : YoungTableau μ) :
    Submodule (MonoidAlgebra k (𝓢 μ.card)) (MonoidAlgebra k (𝓢 μ.card)) :=
  Submodule.span (MonoidAlgebra k (𝓢 μ.card)) {γ k T}
abbrev V (T : YoungTableau μ) := SpechtModule k T

theorem specht_module_irr (T : YoungTableau μ) (hcard : IsUnit ↑(Fintype.card (𝓢 μ.card))):
    IsSimpleModule (MonoidAlgebra k (𝓢 μ.card)) (V k T) := by
  sorry

#check Representation k (𝓢 μ.card)

end
