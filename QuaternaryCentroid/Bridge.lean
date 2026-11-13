module
public import Mathlib
public import LorentzLie.Centroid
public import LorentzLie.FormDefs
public import LorentzLie.FormCentroid
public import LorentzLie.QuarticField
public import HermiteCompositum.Assembly

@[expose] public section
/-!
# Helper theorems for the compared statements

The proofs of the eleven compared statements (`Solution.lean`) from the libraries `LorentzLie` and
`HermiteCompositum`. Every declaration here is in the namespace `QuaternaryCentroid.Bridge` and is
stated with the library's `LorentzLie.IsBracketCommuting`, which has the same body as the
definition `QuaternaryCentroid.IsBracketCommuting` carried by `Challenge.lean` and `Solution.lean`.

* Statement 1: `lead`, from `LorentzLie.exists_hodge_of_basis` and
  `LorentzLie.hodge_of_basis_eq_or_eq_neg`.
* Statement 2: `squares`; clauses (c) and (d), on idempotents, are proved here for every form
  (`halfOp`, `idempotent_coeffs`).
* Statement 4: `isometry_det`, `exists_conj_lieEquiv`, `isometry_conj_of_basis`,
  `exists_isometry_det_neg_one`, proved here for every form: an orthogonal basis
  (`exists_orthogonal_basis_four`), the explicit operator of the library on a diagonal form, the sign
  of the conjugated operator (`conj_eq_or_eq_neg_of_description`), and one matrix entry that
  identifies the sign with the determinant (`star0_conj_entry`, `sign_mul_det_diag`).
* Statement 7: `real_diagonal`, with `idempotent_description` for the case of square `1`.
* Statements 9, 10, 11: `discr_of_root`, `root_instance`, `not_lieEquiv_diag`, `exists_root`,
  `scalar_control`.

The line `attribute [local instance] LieRing.ofAssociativeRing` below is local to the section
`Helpers`: the libraries state their theorems with it. `Challenge.lean` and `Solution.lean` do not
declare it, and each compared statement is closed there by a theorem of this file, whose statement
is definitionally equal.
-/

set_option autoImplicit false

section Helpers

attribute [local instance] LieRing.ofAssociativeRing

namespace QuaternaryCentroid.Bridge

open LorentzLie

/-! ### Statement 1 -/

theorem lead {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype ι] [DecidableEq ι] (h2 : (2 : F) ≠ 0) (hι : Fintype.card ι = 4)
    (b : Module.Basis ι F V) (B : LinearMap.BilinForm F V) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) :
    ∃ H : skewAdjointLieSubalgebra B →ₗ[F] skewAdjointLieSubalgebra B,
      IsBracketCommuting H ∧
      (∀ X, H (H X) = (LinearMap.BilinForm.toMatrix b B).det • X) ∧
      (∀ R : skewAdjointLieSubalgebra B →ₗ[F] skewAdjointLieSubalgebra B, IsBracketCommuting R →
        ∃! ab : F × F, R = ab.1 • LinearMap.id + ab.2 • H) ∧
      ∀ H' : skewAdjointLieSubalgebra B →ₗ[F] skewAdjointLieSubalgebra B,
        IsBracketCommuting H' → (¬ ∃ a : F, H' = a • LinearMap.id) →
        (∀ X, H' (H' X) = (LinearMap.BilinForm.toMatrix b B).det • X) → H' = H ∨ H' = -H := by
  obtain ⟨H, hc, hsq, hu⟩ := exists_hodge_of_basis h2 hι b B hB hnd
  exact ⟨H, hc, hsq, hu, fun H' hH' hs hsq' =>
    hodge_of_basis_eq_or_eq_neg h2 hι b B hB hnd H H' hc (FormCentroid.not_scalar H hc hu) hsq
      hH' hs hsq'⟩

/-! ### Statement 2 -/

/-- `halfOp H s = ½ (id + s⁻¹ • H)`. -/
noncomputable def halfOp {E M : Type*} [Field E] [AddCommGroup M] [Module E M] (H : M →ₗ[E] M)
    (s : E) : M →ₗ[E] M :=
  (2 : E)⁻¹ • (LinearMap.id + s⁻¹ • H)

theorem halfOp_halfOp {E M : Type*} [Field E] [AddCommGroup M] [Module E M]
    (H : M →ₗ[E] M) (d s : E) (hs : s * s = d) (hs0 : s ≠ 0)
    (hsq : ∀ X : M, H (H X) = d • X) (X : M) :
    halfOp H s (halfOp H s X) = halfOp H s X := by
  subst hs
  simp only [halfOp, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, map_add,
    map_smul, hsq]
  by_cases h2 : (2 : E) = 0
  · simp [h2]
  · match_scalars <;> field_simp <;> ring

theorem isBracketCommuting_halfOp {E L : Type*} [Field E] [LieRing L] [LieAlgebra E L]
    (H : L →ₗ[E] L) (hH : IsBracketCommuting H) (s : E) : IsBracketCommuting (halfOp H s) :=
  (isBracketCommuting_id.add (hH.smul _)).smul _

/-- A bracket-commuting idempotent other than `0` and `id` is `½ • id + β • H` with
`4 β² d = 1`. -/
theorem idempotent_coeffs {F L : Type*} [Field F] [LieRing L] [LieAlgebra F L]
    (H : L →ₗ[F] L) (d : F) (hc : IsBracketCommuting H) (hsq : ∀ X, H (H X) = d • X)
    (hu : ∀ R : L →ₗ[F] L, IsBracketCommuting R →
      ∃! ab : F × F, R = ab.1 • LinearMap.id + ab.2 • H)
    (P : L →ₗ[F] L) (hP : IsBracketCommuting P) (hP0 : P ≠ 0) (hP1 : P ≠ LinearMap.id)
    (hPP : ∀ X, P (P X) = P X) :
    ∃ β : F, P = (2 : F)⁻¹ • LinearMap.id + β • H ∧ 4 * β ^ 2 * d = 1 := by
  obtain ⟨⟨a, b⟩, hab, -⟩ := hu P hP
  dsimp only at hab
  have h : a • (LinearMap.id : L →ₗ[F] L) + b • H =
      (a ^ 2 + b ^ 2 * d) • LinearMap.id + (2 * a * b) • H := by
    refine LinearMap.ext fun X => ?_
    have h3 := hPP X
    rw [hab, FormCentroid.sq_apply H d hsq a b X] at h3
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    exact h3.symm
  obtain ⟨h4, h5⟩ := FormCentroid.pair_unique H hc hu _ _ _ _ h
  have hb : b ≠ 0 := by
    intro hb
    rw [hb] at h4
    have ha : a * (a - 1) = 0 := by linear_combination -h4
    rcases mul_eq_zero.mp ha with h0 | h1
    · exact hP0 (by rw [hab, hb, h0, zero_smul, zero_smul, add_zero])
    · exact hP1 (by rw [hab, hb, sub_eq_zero.mp h1, zero_smul, one_smul, add_zero])
  have h7 : 2 * a = 1 := by
    have h8 : b * (2 * a - 1) = 0 := by linear_combination -h5
    rcases mul_eq_zero.mp h8 with h9 | h9
    · exact absurd h9 hb
    · linear_combination h9
  have h6 : 4 * b ^ 2 * d = 1 := by linear_combination (-4) * h4 - (2 * a - 1) * h7
  have ha : a = (2 : F)⁻¹ := eq_inv_of_mul_eq_one_left (by linear_combination h7)
  exact ⟨b, by rw [hab, ha], h6⟩

theorem squares {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype ι] [DecidableEq ι] (h2 : (2 : F) ≠ 0) (hι : Fintype.card ι = 4)
    (b : Module.Basis ι F V) (B : LinearMap.BilinForm F V) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) :
    (∀ c : F,
      (∃ R : skewAdjointLieSubalgebra B →ₗ[F] skewAdjointLieSubalgebra B,
          IsBracketCommuting R ∧ (¬ ∃ a : F, R = a • LinearMap.id) ∧ ∀ X, R (R X) = c • X) ↔
        ∃ t : F, t ≠ 0 ∧ c = t ^ 2 * (LinearMap.BilinForm.toMatrix b B).det) ∧
    ((∃ R : skewAdjointLieSubalgebra B →ₗ[F] skewAdjointLieSubalgebra B,
          IsBracketCommuting R ∧ ∀ X, R (R X) = -X) ↔
        IsSquare (-(LinearMap.BilinForm.toMatrix b B).det) ∨ IsSquare (-1 : F)) ∧
    ((∃ P : skewAdjointLieSubalgebra B →ₗ[F] skewAdjointLieSubalgebra B,
          IsBracketCommuting P ∧ P ≠ 0 ∧ P ≠ LinearMap.id ∧ ∀ X, P (P X) = P X) ↔
        IsSquare (LinearMap.BilinForm.toMatrix b B).det) ∧
    ∀ P Q : skewAdjointLieSubalgebra B →ₗ[F] skewAdjointLieSubalgebra B,
      IsBracketCommuting P → P ≠ 0 → P ≠ LinearMap.id → (∀ X, P (P X) = P X) →
      IsBracketCommuting Q → Q ≠ 0 → Q ≠ LinearMap.id → (∀ X, Q (Q X) = Q X) →
      Q = P ∨ Q = LinearMap.id - P := by
  have hd : (LinearMap.BilinForm.toMatrix b B).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd
  obtain ⟨H, hc, hsq, hu⟩ := exists_hodge_of_basis h2 hι b B hB hnd
  refine ⟨fun c => exists_nonscalar_sq_iff h2 hι b B hB hnd c,
    exists_sq_neg_one_iff h2 hι b B hB hnd, ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨P, hP, hP0, hP1, hPP⟩
    obtain ⟨β, -, h6⟩ := idempotent_coeffs H _ hc hsq hu P hP hP0 hP1 hPP
    exact ⟨2 * β * (LinearMap.BilinForm.toMatrix b B).det, by
      linear_combination (-(LinearMap.BilinForm.toMatrix b B).det) * h6⟩
  · rintro ⟨s, hs⟩
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hs
      exact hd hs
    have hns : ¬ ∃ a : F, halfOp H s = a • LinearMap.id := by
      rintro ⟨a, ha⟩
      unfold halfOp at ha
      have h : ((2 : F)⁻¹) • (LinearMap.id : skewAdjointLieSubalgebra B →ₗ[F] _) +
          ((2 : F)⁻¹ * s⁻¹) • H = a • LinearMap.id + (0 : F) • H := by
        rw [zero_smul, add_zero, ← ha, smul_add, smul_smul]
      exact (mul_ne_zero (inv_ne_zero h2) (inv_ne_zero hs0))
        (FormCentroid.pair_unique H hc hu _ _ _ _ h).2
    exact ⟨halfOp H s, isBracketCommuting_halfOp H hc s,
      fun h0 => hns ⟨0, by rw [h0, zero_smul]⟩, fun h1 => hns ⟨1, by rw [h1, one_smul]⟩,
      fun X => halfOp_halfOp H _ s hs.symm hs0 hsq X⟩
  · intro P Q hP hP0 hP1 hPP hQ hQ0 hQ1 hQQ
    obtain ⟨β, hPβ, h6⟩ := idempotent_coeffs H _ hc hsq hu P hP hP0 hP1 hPP
    obtain ⟨γ, hQγ, h6'⟩ := idempotent_coeffs H _ hc hsq hu Q hQ hQ0 hQ1 hQQ
    have h4ne : (4 : F) ≠ 0 := by
      have h44 : (4 : F) = 2 * 2 := by norm_num
      rw [h44]
      exact mul_ne_zero h2 h2
    have h8 : (γ - β) * (γ + β) = 0 := by
      have h9 : ((γ - β) * (γ + β)) * (4 * (LinearMap.BilinForm.toMatrix b B).det) = 0 := by
        linear_combination h6' - h6
      exact (mul_eq_zero.mp h9).resolve_right (mul_ne_zero h4ne hd)
    rcases mul_eq_zero.mp h8 with h | h
    · left
      rw [hQγ, hPβ, sub_eq_zero.mp h]
    · right
      have hγ : γ = -β := eq_neg_of_add_eq_zero_left h
      have hinv : (2 : F)⁻¹ + (2 : F)⁻¹ = 1 := by rw [← two_mul, mul_inv_cancel₀ h2]
      have h3 : ((2 : F)⁻¹ • (LinearMap.id : skewAdjointLieSubalgebra B →ₗ[F] _) + -β • H) +
          ((2 : F)⁻¹ • LinearMap.id + β • H) = ((2 : F)⁻¹ + (2 : F)⁻¹) • LinearMap.id := by
        module
      rw [eq_sub_iff_add_eq, hQγ, hPβ, hγ, h3, hinv, one_smul]

/-! ### Statement 4 -/

/-- Conjugation by a Lie algebra equivalence sends a bracket-commuting map with scalar square to
itself or to its negative (from a description by one operator). -/
theorem conj_eq_or_eq_neg_of_description {F L : Type*} [Field F] [LieRing L] [LieAlgebra F L]
    (h2 : (2 : F) ≠ 0) (H : L →ₗ[F] L) (d : F) (hd : d ≠ 0) (hc : IsBracketCommuting H)
    (hsq : ∀ X, H (H X) = d • X)
    (hu : ∀ R : L →ₗ[F] L, IsBracketCommuting R →
      ∃! ab : F × F, R = ab.1 • LinearMap.id + ab.2 • H)
    (φ : L ≃ₗ⁅F⁆ L) (H₀ : L →ₗ[F] L) (hH₀ : IsBracketCommuting H₀) (c : F)
    (hH₀2 : ∀ X, H₀ (H₀ X) = c • X) :
    (∀ X, φ (H₀ (φ.symm X)) = H₀ X) ∨ (∀ X, φ (H₀ (φ.symm X)) = -H₀ X) := by
  by_cases hs : ∃ a : F, H₀ = a • LinearMap.id
  · obtain ⟨a, rfl⟩ := hs
    left
    intro X
    simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, LieEquiv.apply_symm_apply]
  · obtain ⟨t, ht, hHt, hct⟩ :=
      FormCentroid.eq_smul_of_nonscalar_sq h2 H d hc hsq hu c H₀ hH₀ hs hH₀2
    obtain ⟨-, -, hu'⟩ := FormCentroid.description_smul H d t ht hc hsq hu
    rw [← hHt] at hu'
    have hc0 : c ≠ 0 := by rw [hct]; exact mul_ne_zero (pow_ne_zero 2 ht) hd
    have hconj := hH₀.lieEquivConj φ
    have hns : ¬ ∃ a : F, ((φ.toLinearEquiv : L →ₗ[F] L) ∘ₗ H₀ ∘ₗ
        (φ.symm.toLinearEquiv : L →ₗ[F] L)) = a • LinearMap.id := by
      rintro ⟨a, ha⟩
      apply hs
      refine ⟨a, LinearMap.ext fun Y => ?_⟩
      have h1 := LinearMap.congr_fun ha (φ Y)
      change φ (H₀ (φ.symm (φ Y))) = a • φ Y at h1
      rw [LieEquiv.symm_apply_apply, ← map_smul] at h1
      exact φ.injective h1
    have hsq' : ∀ X, ((φ.toLinearEquiv : L →ₗ[F] L) ∘ₗ H₀ ∘ₗ
        (φ.symm.toLinearEquiv : L →ₗ[F] L)) (((φ.toLinearEquiv : L →ₗ[F] L) ∘ₗ H₀ ∘ₗ
        (φ.symm.toLinearEquiv : L →ₗ[F] L)) X) = c • X := by
      intro X
      change φ (H₀ (φ.symm (φ (H₀ (φ.symm X))))) = c • X
      rw [LieEquiv.symm_apply_apply, hH₀2, map_smul, LieEquiv.apply_symm_apply]
    rcases FormCentroid.eq_or_eq_neg_of_description h2 H₀ c hc0 hH₀ hH₀2 hu' _ hconj hns hsq'
      with h | h
    · left; intro X; exact LinearMap.congr_fun h X
    · right; intro X; exact LinearMap.congr_fun h X

/-- The antisymmetric matrix `E₀₁ - E₁₀`. -/
def B₀ (F : Type*) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

/-- One entry of `N * star0 (Nᵀ * B * N) * Nᵀ = det N • star0 B`, at `B = B₀`. -/
theorem star0_conj_entry {F : Type*} [Field F] (N : Matrix (Fin 4) (Fin 4) F) :
    (N * star0 (N.transpose * B₀ F * N) * N.transpose : Matrix (Fin 4) (Fin 4) F) 2 3 =
      N.det := by
  rw [Matrix.det_succ_row_zero]
  simp [B₀, Matrix.det_fin_three, star0, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.transpose_apply, Matrix.submatrix_apply, Fin.succAbove]
  ring

theorem mem_skew_iff {F : Type*} [Field F] (G X : Matrix (Fin 4) (Fin 4) F) :
    X ∈ skewAdjointMatricesLieSubalgebra G ↔ X.transpose * G = -(G * X) := by
  rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  unfold Matrix.IsSkewAdjoint Matrix.IsAdjointPair
  rw [Matrix.mul_neg]

/-- For a matrix `M` preserving `diagonal η` and `φ` conjugation by `M`: if `φ ∘ hodge η ∘ φ⁻¹`
is `σ • hodge η`, then `σ * det M = 1`. -/
theorem sign_mul_det_diag {F : Type*} [Field F] (η : Fin 4 → F) (hη : ∀ i, η i ≠ 0)
    (M : Matrix (Fin 4) (Fin 4) F)
    (hM : M.transpose * Matrix.diagonal η * M = Matrix.diagonal η)
    (φ : etaSkew η ≃ₗ⁅F⁆ etaSkew η)
    (hφ : ∀ X : etaSkew η,
      (φ X : Matrix (Fin 4) (Fin 4) F) * M = M * (X : Matrix (Fin 4) (Fin 4) F))
    (σ : F) (hσ : ∀ X, φ (hodge η (φ.symm X)) = σ • hodge η X) : σ * M.det = 1 := by
  obtain ⟨Di, hDD, hDD'⟩ : ∃ Di : Matrix (Fin 4) (Fin 4) F,
      Matrix.diagonal η * Di = 1 ∧ Di.transpose * Matrix.diagonal η = 1 := by
    refine ⟨Matrix.diagonal fun i => (η i)⁻¹, ?_, ?_⟩
    · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact mul_inv_cancel₀ (hη i)
    · rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact inv_mul_cancel₀ (hη i)
  have hp : (Matrix.diagonal η).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hη i
  have hdet : M.det * M.det = 1 := by
    have h := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
    have h3 : (M.det * M.det - 1) * (Matrix.diagonal η).det = 0 := by linear_combination h
    rcases mul_eq_zero.mp h3 with h4 | h4
    · linear_combination h4
    · exact absurd h4 hp
  have hu0 : M.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdet
    exact zero_ne_one hdet
  have hMN : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hu0)
  have hNM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hu0)
  have hdN : M⁻¹.det = M.det := by
    have h := congrArg Matrix.det hMN
    rw [Matrix.det_mul, Matrix.det_one] at h
    have h3 : M.det * (M⁻¹.det - M.det) = 0 := by linear_combination h - hdet
    rcases mul_eq_zero.mp h3 with h0 | h0
    · exact absurd h0 hu0
    · exact sub_eq_zero.mp h0
  generalize M⁻¹ = N at hMN hNM hdN
  have h1 : M.transpose * Matrix.diagonal η = Matrix.diagonal η * N := by
    calc M.transpose * Matrix.diagonal η = M.transpose * Matrix.diagonal η * (M * N) := by
          rw [hMN, Matrix.mul_one]
      _ = (M.transpose * Matrix.diagonal η * M) * N := by simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal η * N := by rw [hM]
  have h2 : Matrix.diagonal η * M = N.transpose * Matrix.diagonal η := by
    have h := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.diagonal_transpose] at h
    exact h
  obtain ⟨X₀, hGX⟩ : ∃ X₀ : etaSkew η,
      Matrix.diagonal η * (X₀ : Matrix (Fin 4) (Fin 4) F) = B₀ F := by
    refine ⟨⟨Di * B₀ F, ?_⟩, ?_⟩
    · rw [mem_skew_iff, Matrix.transpose_mul, Matrix.mul_assoc, hDD', Matrix.mul_one,
        ← Matrix.mul_assoc, hDD, Matrix.one_mul]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [B₀, Matrix.transpose_apply]
    · change Matrix.diagonal η * (Di * B₀ F) = B₀ F
      rw [← Matrix.mul_assoc, hDD, Matrix.one_mul]
  have e1 := hφ X₀
  have e2 := hφ (hodge η X₀)
  have e3 := hσ (φ X₀)
  rw [LieEquiv.symm_apply_apply] at e3
  have e3' : (φ (hodge η X₀) : Matrix (Fin 4) (Fin 4) F) =
      σ • (star0 (Matrix.diagonal η * (φ X₀ : Matrix (Fin 4) (Fin 4) F)) * Matrix.diagonal η) := by
    rw [e3]
    rfl
  have hY : (φ X₀ : Matrix (Fin 4) (Fin 4) F) = M * (X₀ : Matrix (Fin 4) (Fin 4) F) * N := by
    calc (φ X₀ : Matrix (Fin 4) (Fin 4) F)
        = (φ X₀ : Matrix (Fin 4) (Fin 4) F) * (M * N) := by rw [hMN, Matrix.mul_one]
      _ = ((φ X₀ : Matrix (Fin 4) (Fin 4) F) * M) * N := by rw [Matrix.mul_assoc]
      _ = M * (X₀ : Matrix (Fin 4) (Fin 4) F) * N := by rw [e1]
  have hGY : Matrix.diagonal η * (φ X₀ : Matrix (Fin 4) (Fin 4) F) =
      N.transpose * B₀ F * N := by
    calc Matrix.diagonal η * (φ X₀ : Matrix (Fin 4) (Fin 4) F)
        = (Matrix.diagonal η * M) * (X₀ : Matrix (Fin 4) (Fin 4) F) * N := by
          rw [hY]; simp only [Matrix.mul_assoc]
      _ = N.transpose * (Matrix.diagonal η * (X₀ : Matrix (Fin 4) (Fin 4) F)) * N := by
          rw [h2]; simp only [Matrix.mul_assoc]
      _ = N.transpose * B₀ F * N := by rw [hGX]
  have hZ : (φ (hodge η X₀) : Matrix (Fin 4) (Fin 4) F) =
      M * star0 (B₀ F) * M.transpose * Matrix.diagonal η := by
    calc (φ (hodge η X₀) : Matrix (Fin 4) (Fin 4) F)
        = (φ (hodge η X₀) : Matrix (Fin 4) (Fin 4) F) * (M * N) := by rw [hMN, Matrix.mul_one]
      _ = ((φ (hodge η X₀) : Matrix (Fin 4) (Fin 4) F) * M) * N := by rw [Matrix.mul_assoc]
      _ = M * (star0 (Matrix.diagonal η * (X₀ : Matrix (Fin 4) (Fin 4) F)) *
            Matrix.diagonal η) * N := by
          rw [e2]; rfl
      _ = M * star0 (B₀ F) * M.transpose * Matrix.diagonal η := by
          rw [hGX]; simp only [Matrix.mul_assoc]; rw [h1]
  have h5 : σ • star0 (N.transpose * B₀ F * N) = M * star0 (B₀ F) * M.transpose := by
    have h := e3'.symm.trans hZ
    rw [hGY] at h
    have h' := congrArg (fun A => A * Di) h
    simpa only [Matrix.smul_mul, Matrix.mul_assoc, hDD, Matrix.mul_one] using h'
  have hT : M.transpose * N.transpose = 1 := by
    rw [← Matrix.transpose_mul, hNM, Matrix.transpose_one]
  have h6 : σ • (N * star0 (N.transpose * B₀ F * N) * N.transpose) = star0 (B₀ F) := by
    calc σ • (N * star0 (N.transpose * B₀ F * N) * N.transpose)
        = N * (σ • star0 (N.transpose * B₀ F * N)) * N.transpose := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = N * (M * star0 (B₀ F) * M.transpose) * N.transpose := by rw [h5]
      _ = star0 (B₀ F) := by
          simp only [Matrix.mul_assoc]
          rw [hT, Matrix.mul_one, ← Matrix.mul_assoc, hNM, Matrix.one_mul]
  have h7 := congrFun (congrFun h6 2) 3
  rw [Matrix.smul_apply, star0_conj_entry, hdN, smul_eq_mul] at h7
  have h8 : star0 (B₀ F) 2 3 = 1 := by simp [star0, B₀]
  rw [h8] at h7
  exact h7

/-- The diagonal case: `φ ∘ H₀ ∘ φ⁻¹ = det M • H₀`. -/
theorem isometry_conj_diag {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (η : Fin 4 → F)
    (hη : ∀ i, η i ≠ 0) (M : Matrix (Fin 4) (Fin 4) F)
    (hM : M.transpose * Matrix.diagonal η * M = Matrix.diagonal η)
    (φ : etaSkew η ≃ₗ⁅F⁆ etaSkew η)
    (hφ : ∀ X : etaSkew η,
      (φ X : Matrix (Fin 4) (Fin 4) F) * M = M * (X : Matrix (Fin 4) (Fin 4) F))
    (H₀ : etaSkew η →ₗ[F] etaSkew η) (hH₀ : IsBracketCommuting H₀)
    (hs : ¬ ∃ a : F, H₀ = a • LinearMap.id) (c : F) (hH₀2 : ∀ X, H₀ (H₀ X) = c • X)
    (X : etaSkew η) : φ (H₀ (φ.symm X)) = M.det • H₀ X := by
  obtain ⟨hc, hsq, hu⟩ := FormCentroid.hodge_description h2 η hη
  have hd : (∏ i, η i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hη i
  have key : ∀ Y, φ (hodge η (φ.symm Y)) = M.det • hodge η Y := by
    rcases conj_eq_or_eq_neg_of_description h2 (hodge η) _ hd hc hsq hu φ (hodge η) hc _ hsq
      with h | h
    · have hdm := sign_mul_det_diag η hη M hM φ hφ 1 (fun Y => by rw [h Y, one_smul])
      rw [one_mul] at hdm
      intro Y
      rw [h Y, hdm, one_smul]
    · have hdm := sign_mul_det_diag η hη M hM φ hφ (-1) (fun Y => by rw [h Y, neg_one_smul])
      have hd' : M.det = -1 := by linear_combination -hdm
      intro Y
      rw [h Y, hd', neg_one_smul]
  obtain ⟨t, -, hHt, -⟩ :=
    FormCentroid.eq_smul_of_nonscalar_sq h2 (hodge η) _ hc hsq hu c H₀ hH₀ hs hH₀2
  rw [hHt, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, key X, smul_comm]

/-- The same for a matrix `G` equal to a diagonal matrix with nonzero entries. -/
theorem isometry_conj_matrix {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (G : Matrix (Fin 4) (Fin 4) F) (η : Fin 4 → F) (hGη : G = Matrix.diagonal η)
    (hη : ∀ i, η i ≠ 0) (M : Matrix (Fin 4) (Fin 4) F) (hM : M.transpose * G * M = G)
    (φ : skewAdjointMatricesLieSubalgebra G ≃ₗ⁅F⁆ skewAdjointMatricesLieSubalgebra G)
    (hφ : ∀ X : skewAdjointMatricesLieSubalgebra G,
      (φ X : Matrix (Fin 4) (Fin 4) F) * M = M * (X : Matrix (Fin 4) (Fin 4) F))
    (H₀ : skewAdjointMatricesLieSubalgebra G →ₗ[F] skewAdjointMatricesLieSubalgebra G)
    (hH₀ : IsBracketCommuting H₀) (hs : ¬ ∃ a : F, H₀ = a • LinearMap.id) (c : F)
    (hH₀2 : ∀ X, H₀ (H₀ X) = c • X) (X : skewAdjointMatricesLieSubalgebra G) :
    φ (H₀ (φ.symm X)) = M.det • H₀ X := by
  subst hGη
  exact isometry_conj_diag h2 η hη M hM φ hφ H₀ hH₀ hs c hH₀2 X

/-- An orthogonal basis indexed by `Fin 4`: the Gram matrix is diagonal with nonzero entries. -/
theorem exists_orthogonal_basis_four {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype ι] (h2 : (2 : F) ≠ 0) (hι : Fintype.card ι = 4)
    (b : Module.Basis ι F V) (B : LinearMap.BilinForm F V) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) :
    ∃ (w : Module.Basis (Fin 4) F V) (η : Fin 4 → F),
      LinearMap.BilinForm.toMatrix w B = Matrix.diagonal η ∧ ∀ i, η i ≠ 0 := by
  classical
  have : Module.Finite F V := Module.Finite.of_basis b
  let _i2 : Invertible (2 : F) := invertibleOfNonzero h2
  have hfr : Module.finrank F V = 4 := (Module.finrank_eq_card_basis b).trans hι
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.mp hB)
  obtain ⟨w, hw⟩ : ∃ w : Module.Basis (Fin 4) F V, ∀ i j : Fin 4, i ≠ j → B (w i) (w j) = 0 := by
    refine ⟨v.reindex (finCongr hfr), fun i j hij => ?_⟩
    have h4 := hv (i := (finCongr hfr).symm i) (j := (finCongr hfr).symm j)
      (fun h5 => hij ((finCongr hfr).symm.injective h5))
    simpa using h4
  have hG : LinearMap.BilinForm.toMatrix w B = Matrix.diagonal fun i => B (w i) (w i) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, Matrix.diagonal_apply]
    split_ifs with hij
    · rw [hij]
    · exact hw i j hij
  refine ⟨w, fun i => B (w i) (w i), hG, ?_⟩
  have hdet : (LinearMap.BilinForm.toMatrix w B).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero w).mp hnd
  rw [hG, Matrix.det_diagonal] at hdet
  exact fun i => (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ _)

/-- The general form: a linear map `g` preserving a symmetric nondegenerate form `B` on a
four-dimensional space, `φ` conjugation by `g` on the `B`-skew-adjoint endomorphisms. -/
theorem isometry_conj_of_basis {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype ι] (h2 : (2 : F) ≠ 0) (hι : Fintype.card ι = 4)
    (b : Module.Basis ι F V) (B : LinearMap.BilinForm F V) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) (g : V →ₗ[F] V) (hg : ∀ x y : V, B (g x) (g y) = B x y)
    (φ : skewAdjointLieSubalgebra B ≃ₗ⁅F⁆ skewAdjointLieSubalgebra B)
    (hφ : ∀ (X : skewAdjointLieSubalgebra B) (x : V),
      (φ X : Module.End F V) (g x) = g ((X : Module.End F V) x))
    (H₀ : skewAdjointLieSubalgebra B →ₗ[F] skewAdjointLieSubalgebra B)
    (hH₀ : IsBracketCommuting H₀) (hs : ¬ ∃ a : F, H₀ = a • LinearMap.id)
    (c : F) (hH₀2 : ∀ X, H₀ (H₀ X) = c • X) (X : skewAdjointLieSubalgebra B) :
    φ (H₀ (φ.symm X)) = LinearMap.det g • H₀ X := by
  classical
  obtain ⟨w, η, hG, hη⟩ := exists_orthogonal_basis_four h2 hι b B hB hnd
  obtain ⟨e, he⟩ : ∃ e : skewAdjointLieSubalgebra B ≃ₗ⁅F⁆
        skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix w B),
      ∀ Y : skewAdjointLieSubalgebra B,
        (e Y : Matrix (Fin 4) (Fin 4) F) = LinearMap.toMatrix w w (Y : Module.End F V) :=
    ⟨FormCentroid.skewAdjointEquivMatrices w B, fun Y => rfl⟩
  have hM : (LinearMap.toMatrix w w g).transpose * LinearMap.BilinForm.toMatrix w B *
      LinearMap.toMatrix w w g = LinearMap.BilinForm.toMatrix w B := by
    have h1 : LinearMap.BilinForm.toMatrix w (B.comp g g) = LinearMap.BilinForm.toMatrix w B := by
      congr 1
      exact LinearMap.ext₂ hg
    rw [LinearMap.BilinForm.toMatrix_comp w w] at h1
    exact h1
  have hφ' : ∀ Y : skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix w B),
      ((e.symm.trans (φ.trans e)) Y : Matrix (Fin 4) (Fin 4) F) * LinearMap.toMatrix w w g =
        LinearMap.toMatrix w w g * (Y : Matrix (Fin 4) (Fin 4) F) := by
    intro Y
    have hZ : ((e.symm.trans (φ.trans e)) Y : Matrix (Fin 4) (Fin 4) F) =
        LinearMap.toMatrix w w ((φ (e.symm Y) : skewAdjointLieSubalgebra B) : Module.End F V) :=
      he (φ (e.symm Y))
    have hYm : (Y : Matrix (Fin 4) (Fin 4) F) =
        LinearMap.toMatrix w w ((e.symm Y : skewAdjointLieSubalgebra B) : Module.End F V) :=
      (congrArg Subtype.val (e.apply_symm_apply Y)).symm.trans (he (e.symm Y))
    rw [hZ, hYm, ← LinearMap.toMatrix_comp w w w, ← LinearMap.toMatrix_comp w w w]
    congr 1
    exact LinearMap.ext fun x => hφ (e.symm Y) x
  have hns : ¬ ∃ a : F, ((e.toLinearEquiv : skewAdjointLieSubalgebra B →ₗ[F]
        skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix w B)) ∘ₗ H₀ ∘ₗ
      (e.symm.toLinearEquiv :
        skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix w B) →ₗ[F] skewAdjointLieSubalgebra B)) = a • LinearMap.id := by
    rintro ⟨a, ha⟩
    apply hs
    refine ⟨a, LinearMap.ext fun Y => ?_⟩
    have h1 := LinearMap.congr_fun ha (e Y)
    change e (H₀ (e.symm (e Y))) = a • e Y at h1
    rw [LieEquiv.symm_apply_apply, ← map_smul] at h1
    exact e.injective h1
  have hsq' : ∀ Y, ((e.toLinearEquiv : skewAdjointLieSubalgebra B →ₗ[F]
        skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix w B)) ∘ₗ H₀ ∘ₗ
      (e.symm.toLinearEquiv :
        skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix w B) →ₗ[F] skewAdjointLieSubalgebra B))
      (((e.toLinearEquiv : skewAdjointLieSubalgebra B →ₗ[F]
        skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix w B)) ∘ₗ H₀ ∘ₗ
      (e.symm.toLinearEquiv :
        skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix w B) →ₗ[F] skewAdjointLieSubalgebra B)) Y) = c • Y := by
    intro Y
    change e (H₀ (e.symm (e (H₀ (e.symm Y))))) = c • Y
    rw [LieEquiv.symm_apply_apply, hH₀2, map_smul, LieEquiv.apply_symm_apply]
  have key := isometry_conj_matrix h2 _ η hG hη (LinearMap.toMatrix w w g) hM
    (e.symm.trans (φ.trans e)) hφ' _ (hH₀.lieEquivConj e) hns c hsq' (e X)
  change e (φ (e.symm (e (H₀ (e.symm (e (φ.symm (e.symm (e X))))))))) =
    (LinearMap.toMatrix w w g).det • e (H₀ (e.symm (e X))) at key
  simp only [LieEquiv.symm_apply_apply] at key
  rw [← map_smul] at key
  rw [e.injective key, LinearMap.det_toMatrix w g]

/-- A linear map preserving a nondegenerate form has determinant `1` or `-1`. -/
theorem isometry_det {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V] [Fintype ι]
    (b : Module.Basis ι F V) (B : LinearMap.BilinForm F V) (hnd : B.Nondegenerate)
    (g : V →ₗ[F] V) (hg : ∀ x y : V, B (g x) (g y) = B x y) :
    LinearMap.det g = 1 ∨ LinearMap.det g = -1 := by
  classical
  have hdet : (LinearMap.BilinForm.toMatrix b B).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd
  have h1 : LinearMap.BilinForm.toMatrix b (B.comp g g) = LinearMap.BilinForm.toMatrix b B := by
    congr 1
    exact LinearMap.ext₂ hg
  rw [LinearMap.BilinForm.toMatrix_comp b b] at h1
  have h := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix b g] at h
  have h3 : (LinearMap.det g - 1) * (LinearMap.det g + 1) *
      (LinearMap.BilinForm.toMatrix b B).det = 0 := by linear_combination h
  rcases mul_eq_zero.mp h3 with h4 | h4
  · rcases mul_eq_zero.mp h4 with h5 | h5
    · left; exact sub_eq_zero.mp h5
    · right; exact eq_neg_of_add_eq_zero_left h5
  · exact absurd h4 hdet

theorem mem_so_iff {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (B : LinearMap.BilinForm F V) (f : Module.End F V) :
    f ∈ skewAdjointLieSubalgebra B ↔ ∀ x y, B (f x) y = -B x (f y) := by
  change f ∈ B.skewAdjointSubmodule ↔ _
  rw [LinearMap.mem_skewAdjointSubmodule]
  unfold LinearMap.IsSkewAdjoint LinearMap.IsAdjointPair
  simp only [Pi.neg_apply, map_neg]

/-- Conjugation by a linear map preserving a nondegenerate form is a Lie algebra equivalence of
the skew-adjoint endomorphisms. -/
theorem exists_conj_lieEquiv {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V] [Fintype ι]
    (b : Module.Basis ι F V) (B : LinearMap.BilinForm F V) (hnd : B.Nondegenerate)
    (g : V →ₗ[F] V) (hg : ∀ x y : V, B (g x) (g y) = B x y) :
    ∃ φ : skewAdjointLieSubalgebra B ≃ₗ⁅F⁆ skewAdjointLieSubalgebra B,
      ∀ (X : skewAdjointLieSubalgebra B) (x : V),
        (φ X : Module.End F V) (g x) = g ((X : Module.End F V) x) := by
  have : Module.Finite F V := Module.Finite.of_basis b
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine hnd.1 x fun y => ?_
    rw [← hg x y, hx, map_zero, LinearMap.zero_apply]
  obtain ⟨gE, hgE⟩ : ∃ gE : V ≃ₗ[F] V, ∀ x, gE x = g x :=
    ⟨LinearEquiv.ofInjectiveEndo g hinj, fun x => rfl⟩
  have hg' : ∀ x y : V, B (gE x) (gE y) = B x y := fun x y => by rw [hgE, hgE, hg]
  refine ⟨LieEquiv.ofSubalgebras _ _ gE.lieConj ?_, fun X x => ?_⟩
  · ext f
    rw [LieSubalgebra.mem_map]
    constructor
    · rintro ⟨X, hX, rfl⟩
      rw [mem_so_iff] at hX ⊢
      intro x y
      change B (gE (X (gE.symm x))) y = -B x (gE (X (gE.symm y)))
      calc B (gE (X (gE.symm x))) y = B (gE (X (gE.symm x))) (gE (gE.symm y)) := by
            rw [gE.apply_symm_apply]
        _ = B (X (gE.symm x)) (gE.symm y) := hg' _ _
        _ = -B (gE.symm x) (X (gE.symm y)) := hX _ _
        _ = -B (gE (gE.symm x)) (gE (X (gE.symm y))) := by rw [hg']
        _ = -B x (gE (X (gE.symm y))) := by rw [gE.apply_symm_apply]
    · intro hf
      refine ⟨gE.symm.lieConj f, ?_, ?_⟩
      · rw [mem_so_iff] at hf ⊢
        intro x y
        change B (gE.symm (f (gE x))) y = -B x (gE.symm (f (gE y)))
        calc B (gE.symm (f (gE x))) y = B (gE (gE.symm (f (gE x)))) (gE y) := (hg' _ _).symm
          _ = B (f (gE x)) (gE y) := by rw [gE.apply_symm_apply]
          _ = -B (gE x) (f (gE y)) := hf _ _
          _ = -B (gE x) (gE (gE.symm (f (gE y)))) := by rw [gE.apply_symm_apply]
          _ = -B x (gE.symm (f (gE y))) := by rw [hg']
      · refine LinearMap.ext fun x => ?_
        change gE (gE.symm (f (gE (gE.symm x)))) = f x
        rw [gE.apply_symm_apply, gE.apply_symm_apply]
  · change gE ((X : Module.End F V) (gE.symm (g x))) = g ((X : Module.End F V) x)
    rw [← hgE x, gE.symm_apply_apply, hgE]

/-- A linear map of determinant `-1` preserving the form: a reflection in a vector of an
orthogonal basis. -/
theorem exists_isometry_det_neg_one {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype ι] (h2 : (2 : F) ≠ 0) (hι : Fintype.card ι = 4)
    (b : Module.Basis ι F V) (B : LinearMap.BilinForm F V) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) :
    ∃ g : V →ₗ[F] V, (∀ x y : V, B (g x) (g y) = B x y) ∧ LinearMap.det g = -1 := by
  obtain ⟨w, η, hG, -⟩ := exists_orthogonal_basis_four h2 hι b B hB hnd
  refine ⟨Matrix.toLin w w (Matrix.diagonal ![-1, 1, 1, 1]), fun x y => ?_, ?_⟩
  · have h1 : LinearMap.BilinForm.toMatrix w
        (B.comp (Matrix.toLin w w (Matrix.diagonal ![-1, 1, 1, 1]))
          (Matrix.toLin w w (Matrix.diagonal ![-1, 1, 1, 1]))) =
        LinearMap.BilinForm.toMatrix w B := by
      rw [LinearMap.BilinForm.toMatrix_comp w w, LinearMap.toMatrix_toLin, hG,
        Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      fin_cases i <;> simp
    exact LinearMap.congr_fun₂ ((LinearMap.BilinForm.toMatrix w).injective h1) x y
  · rw [LinearMap.det_toLin, Matrix.det_diagonal]
    simp [Fin.prod_univ_four]

/-! ### Statement 7 -/

/-- From a description by an operator of square `1`: an idempotent `P` with every
bracket-commuting map uniquely `x • P + y • (id - P)`. -/
theorem idempotent_description {F L : Type*} [Field F] [LieRing L] [LieAlgebra F L]
    (h2 : (2 : F) ≠ 0) (H : L →ₗ[F] L) (hc : IsBracketCommuting H)
    (hsq : ∀ X, H (H X) = (1 : F) • X)
    (hu : ∀ R : L →ₗ[F] L, IsBracketCommuting R →
      ∃! ab : F × F, R = ab.1 • LinearMap.id + ab.2 • H) :
    ∃ P : L →ₗ[F] L, IsBracketCommuting P ∧ P ≠ 0 ∧ P ≠ LinearMap.id ∧ (∀ X, P (P X) = P X) ∧
      ∀ R : L →ₗ[F] L, IsBracketCommuting R →
        ∃! ab : F × F, R = ab.1 • P + ab.2 • (LinearMap.id - P) := by
  have hinv : (2 : F)⁻¹ + (2 : F)⁻¹ = 1 := by rw [← two_mul, mul_inv_cancel₀ h2]
  have hP : halfOp H 1 = (2 : F)⁻¹ • (LinearMap.id + H) := by
    unfold halfOp
    rw [inv_one, one_smul]
  have hQ : LinearMap.id - halfOp H 1 = (2 : F)⁻¹ • (LinearMap.id - H) := by
    have hsum : (2 : F)⁻¹ • (LinearMap.id - H) + (2 : F)⁻¹ • (LinearMap.id + H) =
        ((2 : F)⁻¹ + (2 : F)⁻¹) • (LinearMap.id : L →ₗ[F] L) := by module
    rw [hP, sub_eq_iff_eq_add, hsum, hinv, one_smul]
  have key : ∀ x y : F, x • halfOp H 1 + y • (LinearMap.id - halfOp H 1) =
      ((x + y) * (2 : F)⁻¹) • (LinearMap.id : L →ₗ[F] L) + ((x - y) * (2 : F)⁻¹) • H := by
    intro x y
    rw [hQ, hP]
    module
  have hns : ¬ ∃ a : F, halfOp H 1 = a • LinearMap.id := by
    rintro ⟨a, ha⟩
    rw [hP] at ha
    have h : ((2 : F)⁻¹) • (LinearMap.id : L →ₗ[F] L) + (2 : F)⁻¹ • H =
        a • LinearMap.id + (0 : F) • H := by
      rw [zero_smul, add_zero, ← ha, smul_add]
    exact (inv_ne_zero h2) (FormCentroid.pair_unique H hc hu _ _ _ _ h).2
  refine ⟨halfOp H 1, isBracketCommuting_halfOp H hc 1, fun h0 => hns ⟨0, by rw [h0, zero_smul]⟩,
    fun h1 => hns ⟨1, by rw [h1, one_smul]⟩,
    fun X => halfOp_halfOp H 1 1 (mul_one 1) one_ne_zero hsq X, ?_⟩
  intro R hR
  obtain ⟨⟨a, b⟩, hab, huniq⟩ := hu R hR
  dsimp only at hab
  refine ⟨(a + b, a - b), ?_, ?_⟩
  · dsimp only
    have e1 : (a + b + (a - b)) * (2 : F)⁻¹ = a := by linear_combination a * hinv
    have e2 : (a + b - (a - b)) * (2 : F)⁻¹ = b := by linear_combination b * hinv
    rw [key, e1, e2]
    exact hab
  · rintro ⟨x, y⟩ hxy
    dsimp only at hxy
    rw [key] at hxy
    have h3 := huniq ((x + y) * (2 : F)⁻¹, (x - y) * (2 : F)⁻¹) hxy
    have h4 : (x + y) * (2 : F)⁻¹ = a := congrArg Prod.fst h3
    have h5 : (x - y) * (2 : F)⁻¹ = b := congrArg Prod.snd h3
    refine Prod.ext ?_ ?_
    · change x = a + b
      linear_combination h4 + h5 - x * hinv
    · change y = a - b
      linear_combination h4 - h5 - y * hinv

theorem real_diagonal (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1) :
    (∏ i, η i = -1 →
      ∃ J : etaSkew η →ₗ[ℝ] etaSkew η,
        IsBracketCommuting J ∧ (∀ X, J (J X) = -X) ∧
        ∀ R : etaSkew η →ₗ[ℝ] etaSkew η, IsBracketCommuting R →
          ∃! ab : ℝ × ℝ, R = ab.1 • LinearMap.id + ab.2 • J) ∧
    (∏ i, η i = 1 →
      ∃ P : etaSkew η →ₗ[ℝ] etaSkew η,
        IsBracketCommuting P ∧ P ≠ 0 ∧ P ≠ LinearMap.id ∧ (∀ X, P (P X) = P X) ∧
        ∀ R : etaSkew η →ₗ[ℝ] etaSkew η, IsBracketCommuting R →
          ∃! ab : ℝ × ℝ, R = ab.1 • P + ab.2 • (LinearMap.id - P)) := by
  have hη0 : ∀ i, η i ≠ 0 := fun i => by rcases hη i with h | h <;> rw [h] <;> norm_num
  obtain ⟨hc, hsq, hu⟩ := FormCentroid.hodge_description (two_ne_zero : (2 : ℝ) ≠ 0) η hη0
  constructor
  · intro h
    exact ⟨hodge η, hc, fun X => by rw [hsq X, h, neg_one_smul], hu⟩
  · intro h
    rw [h] at hsq
    exact idempotent_description two_ne_zero (hodge η) hc hsq hu

/-! ### Statements 9, 10, 11: the field of `x⁴ - x - 1` -/

section Root

open Polynomial NumberField IntermediateField HermiteCompositum HermiteCompositum.Instance

/-- A number field of degree four containing a root of `x⁴ - x - 1` has discriminant `-283`
(from the library `HermiteCompositum`: `minpoly_gen₄`, `finrank_S₄`, `discr_S₄`). -/
theorem discr_of_root (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 4) (θ : K) (hθ : θ ^ 4 = θ + 1) :
    NumberField.discr K = -283 := by
  have hint : IsIntegral ℚ gen₄ := Algebra.IsIntegral.isIntegral gen₄
  let pb : PowerBasis ℚ S₄ := IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral Q)
  have hgen : pb.gen = gen₄ := rfl
  have hroot : aeval θ (minpoly ℚ pb.gen) = 0 := by
    rw [hgen, minpoly_gen₄]
    simp only [Port014.fQ, map_sub, map_pow, aeval_X, map_one]
    rw [hθ]; ring
  let f : S₄ →ₐ[ℚ] K := pb.lift θ hroot
  have hinj : Function.Injective f := f.toRingHom.injective
  have hfin : Module.finrank ℚ S₄ = Module.finrank ℚ K := by rw [finrank_S₄, hK]
  have hbij : Function.Bijective f :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj⟩
  have e : S₄ ≃ₐ[ℚ] K := AlgEquiv.ofBijective f hbij
  rw [← NumberField.discr_eq_discr_of_algEquiv S₄ e, discr_S₄]

theorem exists_root :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (θ : K),
      Module.finrank ℚ K = 4 ∧ θ ^ 4 = θ + 1 := by
  refine ⟨S₄, inferInstance, inferInstance, gen₄, finrank_S₄, ?_⟩
  have h := minpoly.aeval ℚ gen₄
  rw [minpoly_gen₄] at h
  simp only [Port014.fQ, map_sub, map_pow, aeval_X, map_one] at h
  linear_combination h

end Root

theorem root_instance (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 4) (θ : K) (hθ : θ ^ 4 = θ + 1) :
    (∃ H : skewAdjointLieSubalgebra (Algebra.traceForm ℚ K) →ₗ[ℚ]
        skewAdjointLieSubalgebra (Algebra.traceForm ℚ K),
      IsBracketCommuting H ∧ (∀ X, H (H X) = (-283 : ℚ) • X) ∧
      ∀ R : skewAdjointLieSubalgebra (Algebra.traceForm ℚ K) →ₗ[ℚ]
          skewAdjointLieSubalgebra (Algebra.traceForm ℚ K), IsBracketCommuting R →
        ∃! ab : ℚ × ℚ, R = ab.1 • LinearMap.id + ab.2 • H) ∧
    (¬ ∃ R : skewAdjointLieSubalgebra (Algebra.traceForm ℚ K) →ₗ[ℚ]
          skewAdjointLieSubalgebra (Algebra.traceForm ℚ K),
        IsBracketCommuting R ∧ ∀ X, R (R X) = -X) ∧
    ∃ R : skewAdjointMatricesLieSubalgebra
          ((Algebra.traceMatrix ℚ (NumberField.integralBasis K)).map (algebraMap ℚ ℝ)) →ₗ[ℝ]
        skewAdjointMatricesLieSubalgebra
          ((Algebra.traceMatrix ℚ (NumberField.integralBasis K)).map (algebraMap ℚ ℝ)),
      IsBracketCommuting R ∧ ∀ X, R (R X) = -X := by
  have hd := discr_of_root K hK θ hθ
  refine ⟨?_, not_exists_sq_neg_one_of_discr_eq K hK hd, ?_⟩
  · have h := exists_hodge_traceForm K hK
    rw [hd] at h
    have hc : ((-283 : ℤ) : ℚ) = -283 := by norm_num
    rw [hc] at h
    exact h
  · obtain ⟨H, hc, hsq, -⟩ := exists_hodge_traceMatrix_real K hK
    have hpow : (-1 : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces K = -1 := by
      have h1 := QuarticField.discr_eq_neg_one_pow_mul_abs K
      rw [hd] at h1
      rcases neg_one_pow_eq_or ℝ (NumberField.InfinitePlace.nrComplexPlaces K) with h | h
      · rw [h] at h1
        norm_num at h1
      · exact h
    exact ⟨H, hc, fun X => by rw [hsq X, hpow, neg_one_smul]⟩

theorem not_lieEquiv_diag (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 4) (θ : K) (hθ : θ ^ 4 = θ + 1) :
    IsEmpty (skewAdjointLieSubalgebra (Algebra.traceForm ℚ K) ≃ₗ⁅ℚ⁆
        skewAdjointMatricesLieSubalgebra
          (Matrix.diagonal ![1, 1, 1, -1] : Matrix (Fin 4) (Fin 4) ℚ)) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨R, hR, hR2⟩ := diag_exists_sq_neg_one_rat
  refine not_exists_sq_neg_one_of_discr_eq K hK (discr_of_root K hK θ hθ)
    ⟨_, hR.lieEquivConj e.symm, fun X => ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv,
    LieEquiv.symm_symm, LieEquiv.symm_apply_apply, hR2, map_neg, LieEquiv.apply_symm_apply]

theorem scalar_control :
    (∃ R : skewAdjointMatricesLieSubalgebra
          (Matrix.diagonal ![1, 1, 1, -1] : Matrix (Fin 4) (Fin 4) ℚ) →ₗ[ℚ]
        skewAdjointMatricesLieSubalgebra
          (Matrix.diagonal ![1, 1, 1, -1] : Matrix (Fin 4) (Fin 4) ℚ),
      IsBracketCommuting R ∧ ∀ X, R (R X) = (1 : ℚ) • X) ∧
    ¬ ∃ t : ℚ, t ≠ 0 ∧ (1 : ℚ) = t ^ 2 * (-1) := by
  refine ⟨⟨LinearMap.id, fun _ _ => rfl, fun X => by simp⟩, ?_⟩
  rintro ⟨t, -, ht⟩
  nlinarith [sq_nonneg t]

end QuaternaryCentroid.Bridge

end Helpers
