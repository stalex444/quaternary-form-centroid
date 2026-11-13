module
public import Mathlib
public import LorentzLie.Defs
public import LorentzLie.Centroid

@[expose] public section

/-!
# Bracket-commuting maps of the skew-adjoint Lie algebra of a symmetric form

For a symmetric nondegenerate bilinear form `B` on a vector space with a basis indexed by a finite
type, over a field with `2 ≠ 0`, this file describes the linear endomorphisms `R` of
`skewAdjointLieSubalgebra B` with `R ⁅X, Y⁆ = ⁅X, R Y⁆` (`IsBracketCommuting R`).

* `centroid_transport_field` — transport of such a description along a Lie equivalence.
* `exists_hodge_matrix` — matrix form in dimension four: an operator `H` with
  `H (H X) = det G • X`, and every bracket-commuting map is uniquely `a • id + b • H`.
* `exists_hodge_of_basis`, `hodge_of_basis_eq_or_eq_neg` — the same for a form and any basis.
* `exists_nonscalar_sq_iff`, `exists_sq_neg_one_iff`, `det_toMatrix_eq_sq_mul_of_lieEquiv` — the
  squares of the bracket-commuting maps, and the square class of the Gram determinant.
* `centroid_scalar_of_basis` — in every other finite dimension the bracket-commuting maps are
  scalar.

Helper statements are in the namespace `LorentzLie.FormCentroid`.
-/

set_option autoImplicit false

attribute [local instance] LieRing.ofAssociativeRing

namespace LorentzLie

/-! ### D0: transport along a Lie equivalence -/

/-- **D0 (transport of a description of the bracket-commuting maps).** Let `F` be a field, `L` and
`L'` Lie algebras over `F`, and `φ` a Lie algebra equivalence from `L` to `L'`. Let `H'` be an
`F`-linear endomorphism of `L'` and `d` an element of `F` such that: `H'` is bracket-commuting;
`H' (H' X) = d • X` for all `X`; and for every bracket-commuting `F`-linear endomorphism `R` of `L'`
there is exactly one pair `(a, b)` in `F × F` with `R = a • id + b • H'`. Then there is an
`F`-linear endomorphism `H` of `L` with the same three properties on `L`, with the same `d`. -/
theorem centroid_transport_field {F L L' : Type*} [Field F] [LieRing L] [LieAlgebra F L]
    [LieRing L'] [LieAlgebra F L'] (φ : L ≃ₗ⁅F⁆ L') (H' : L' →ₗ[F] L') (d : F)
    (hc : IsBracketCommuting H') (hsq : ∀ X, H' (H' X) = d • X)
    (hu : ∀ R : L' →ₗ[F] L', IsBracketCommuting R →
      ∃! ab : F × F, R = ab.1 • LinearMap.id + ab.2 • H') :
    ∃ H : L →ₗ[F] L, IsBracketCommuting H ∧ (∀ X, H (H X) = d • X) ∧
      ∀ R : L →ₗ[F] L, IsBracketCommuting R →
        ∃! ab : F × F, R = ab.1 • LinearMap.id + ab.2 • H := by
  refine ⟨(φ.symm.toLinearEquiv : L' →ₗ[F] L) ∘ₗ H' ∘ₗ (φ.toLinearEquiv : L →ₗ[F] L'),
    hc.lieEquivConj φ.symm, ?_, ?_⟩
  · intro X
    change φ.symm (H' (φ (φ.symm (H' (φ X))))) = d • X
    rw [LieEquiv.apply_symm_apply, hsq, map_smul, LieEquiv.symm_apply_apply]
  · intro R hR
    obtain ⟨ab, hab, huniq⟩ := hu _ (hR.lieEquivConj φ)
    have key : ∀ (S : L →ₗ[F] L) (cd : F × F),
        S = cd.1 • LinearMap.id + cd.2 •
            ((φ.symm.toLinearEquiv : L' →ₗ[F] L) ∘ₗ H' ∘ₗ (φ.toLinearEquiv : L →ₗ[F] L')) ↔
          (φ.toLinearEquiv : L →ₗ[F] L') ∘ₗ S ∘ₗ (φ.symm.toLinearEquiv : L' →ₗ[F] L) =
            cd.1 • LinearMap.id + cd.2 • H' := by
      intro S cd
      constructor
      · intro h
        ext Y
        change φ (S (φ.symm Y)) = cd.1 • Y + cd.2 • H' Y
        rw [h]
        change φ (cd.1 • φ.symm Y + cd.2 • φ.symm (H' (φ (φ.symm Y)))) = _
        rw [map_add, map_smul, map_smul, LieEquiv.apply_symm_apply,
          LieEquiv.apply_symm_apply]
      · intro h
        ext X
        have h1 := LinearMap.congr_fun h (φ X)
        change φ (S (φ.symm (φ X))) = cd.1 • φ X + cd.2 • H' (φ X) at h1
        rw [LieEquiv.symm_apply_apply] at h1
        change S X = cd.1 • X + cd.2 • φ.symm (H' (φ X))
        refine φ.injective ?_
        change φ (S X) = φ (cd.1 • X + cd.2 • φ.symm (H' (φ X)))
        rw [h1, map_add, map_smul, map_smul, LieEquiv.apply_symm_apply]
    exact ⟨ab, (key R ab).mpr hab, fun cd hcd => huniq cd ((key R cd).mp hcd)⟩

/-! ### Congruence to a diagonal matrix, and the Lie equivalence with `etaSkew` -/

namespace FormCentroid

/-- A symmetric matrix over a field with `2 ≠ 0` is congruent to a diagonal matrix: there are `P`
with `det P ≠ 0` and `η` with `Pᵀ * G * P = diagonal η`. -/
theorem exists_transpose_mul_mul_eq_diagonal {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (h2 : (2 : F) ≠ 0) (G : Matrix ι ι F) (hG : G.IsSymm) :
    ∃ (P : Matrix ι ι F) (η : ι → F), P.det ≠ 0 ∧ P.transpose * G * P = Matrix.diagonal η := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.mp (Matrix.isSymm_toBilin'_iff_isSymm.mpr hG))
  have hcard : Fintype.card (Fin (Module.finrank F (ι → F))) = Fintype.card ι := by simp
  let e : Fin (Module.finrank F (ι → F)) ≃ ι := Fintype.equivOfCardEq hcard
  let w : Module.Basis ι F (ι → F) := v.reindex e
  refine ⟨(Pi.basisFun F ι).toMatrix w, fun i => Matrix.toBilin' G (w i) (w i), ?_, ?_⟩
  · have h1 := Module.Basis.toMatrix_mul_toMatrix_flip (Pi.basisFun F ι) w
    intro h0
    have h3 := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h3
    exact zero_ne_one h3
  · have h := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun F ι) w
      (Matrix.toBilin' G)
    rw [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin'] at h
    rw [h]
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, Matrix.diagonal_apply]
    split_ifs with hij
    · rw [hij]
    · have h4 := hv (i := e.symm i) (j := e.symm j) (fun h5 => hij (e.symm.injective h5))
      simpa [w] using h4

/-- A matrix is `J`-skew exactly when its reindexing along `e` is skew for the reindexed `J`. -/
theorem reindex_mem_skew_iff {F ι κ : Type*} [Field F] [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (J X : Matrix ι ι F) :
    Matrix.reindex e e X ∈ skewAdjointMatricesLieSubalgebra (Matrix.reindex e e J) ↔
      X ∈ skewAdjointMatricesLieSubalgebra J := by
  rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, mem_skewAdjointMatricesSubmodule]
  unfold Matrix.IsSkewAdjoint Matrix.IsAdjointPair
  have h1 : Matrix.reindex e e (X.transpose * J) =
      (Matrix.reindex e e X).transpose * Matrix.reindex e e J := by
    simp only [Matrix.reindex_apply, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
  have h2 : Matrix.reindex e e (J * -X) = Matrix.reindex e e J * -Matrix.reindex e e X := by
    rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
      ← Matrix.submatrix_mul_equiv _ _ _ e.symm]
    rfl
  rw [← h1, ← h2, (Matrix.reindex e e).injective.eq_iff]

/-- The Lie equivalence from the `J`-skew matrices to the skew matrices of the reindexed `J`,
`X ↦ reindex e e X`. -/
noncomputable def skewReindexEquiv {F ι κ : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (J : Matrix ι ι F) :
    skewAdjointMatricesLieSubalgebra J ≃ₗ⁅F⁆
      skewAdjointMatricesLieSubalgebra (Matrix.reindex e e J) :=
  LieEquiv.ofSubalgebras _ _ (Matrix.reindexLieEquiv e) <| by
    ext A
    rw [LieSubalgebra.mem_map]
    constructor
    · rintro ⟨X, hX, rfl⟩
      exact (reindex_mem_skew_iff e J X).mpr hX
    · intro hA
      refine ⟨Matrix.reindex e.symm e.symm A, ?_, ?_⟩
      · rw [← reindex_mem_skew_iff e]
        simpa using hA
      · simp

/-- For a symmetric matrix `G` with `det G ≠ 0` over a field with `2 ≠ 0` and a bijection `e` of
the index type with `κ`: there are `η : κ → F` with all entries nonzero and `t ≠ 0` with
`∏ i, η i = t ^ 2 * det G`, and a Lie equivalence from the `G`-skew matrices to `etaSkew η`. -/
theorem exists_lieEquiv_etaSkew {F ι κ : Type*} [Field F] [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (h2 : (2 : F) ≠ 0) (G : Matrix ι ι F) (hG : G.IsSymm) (hdet : G.det ≠ 0)
    (e : ι ≃ κ) :
    ∃ (η : κ → F) (t : F), t ≠ 0 ∧ (∀ i, η i ≠ 0) ∧ ∏ i, η i = t ^ 2 * G.det ∧
      Nonempty (skewAdjointMatricesLieSubalgebra G ≃ₗ⁅F⁆ etaSkew η) := by
  obtain ⟨P, η₀, hP, hPG⟩ := exists_transpose_mul_mul_eq_diagonal h2 G hG
  have hprod : ∏ i, η₀ i = P.det ^ 2 * G.det := by
    rw [← Matrix.det_diagonal, ← hPG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  refine ⟨η₀ ∘ e.symm, P.det, hP, ?_, ?_, ?_⟩
  · intro i
    have h0 : ∏ i, η₀ i ≠ 0 := by
      rw [hprod]
      exact mul_ne_zero (pow_ne_zero 2 hP) hdet
    exact (Finset.prod_ne_zero_iff.mp h0) (e.symm i) (Finset.mem_univ _)
  · rw [← hprod]
    exact Equiv.prod_comp e.symm η₀
  · have φ1 := skewAdjointMatricesLieSubalgebraEquiv G P
      (Matrix.invertibleOfIsUnitDet P (isUnit_iff_ne_zero.mpr hP))
    rw [hPG] at φ1
    have φ2 := skewReindexEquiv e (Matrix.diagonal η₀)
    have h3 : Matrix.reindex e e (Matrix.diagonal η₀) = Matrix.diagonal (η₀ ∘ e.symm) := by
      rw [Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
    rw [h3] at φ2
    exact ⟨φ1.trans φ2⟩

end FormCentroid

/-! ### Descriptions of the bracket-commuting maps by one operator -/

namespace FormCentroid

/-- Over a field with `2 ≠ 0`, for `η : Fin 4 → F` with nonzero entries: `hodge η` is
bracket-commuting, `hodge η (hodge η X) = (∏ i, η i) • X`, and every bracket-commuting linear map
from `etaSkew η` to itself is `a • id + b • hodge η` for exactly one pair `(a, b)`. -/
theorem hodge_description {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (η : Fin 4 → F)
    (hη : ∀ i, η i ≠ 0) :
    IsBracketCommuting (hodge η) ∧ (∀ X : etaSkew η, hodge η (hodge η X) = (∏ i, η i) • X) ∧
      ∀ R : etaSkew η →ₗ[F] etaSkew η, IsBracketCommuting R →
        ∃! ab : F × F, R = ab.1 • LinearMap.id + ab.2 • hodge η := by
  refine ⟨hodge_lie h2 η hη, hodge_hodge h2 η hη, ?_⟩
  intro R hR
  have h := eq_smul_id_add_smul_hodge h2 η hη R hR
  refine ⟨(_, _), h, ?_⟩
  rintro ⟨a', b'⟩ h'
  dsimp only at h'
  have hz : (a' - (R (gen η 0 1) : Matrix (Fin 4) (Fin 4) F) 0 1 / η 1) •
        (LinearMap.id : etaSkew η →ₗ[F] etaSkew η) +
      (b' - (R (gen η 0 1) : Matrix (Fin 4) (Fin 4) F) 2 3 / (η 0 * η 1 * η 3)) • hodge η = 0 := by
    have h3 := h'.symm.trans h
    rw [← sub_eq_zero] at h3
    rw [← h3]
    module
  obtain ⟨ha, hb⟩ := smul_id_add_smul_hodge_eq_zero η hη _ _ hz
  exact Prod.ext (sub_eq_zero.mp ha) (sub_eq_zero.mp hb)

/-- Rescaling: if `H` is bracket-commuting with `H (H X) = d • X` and every bracket-commuting map
is `a • id + b • H` for exactly one pair `(a, b)`, then for `t ≠ 0` the same three properties hold
for `t • H` with `t ^ 2 * d` in place of `d`. -/
theorem description_smul {F L : Type*} [Field F] [LieRing L] [LieAlgebra F L] (H : L →ₗ[F] L)
    (d t : F) (ht : t ≠ 0) (hc : IsBracketCommuting H) (hsq : ∀ X, H (H X) = d • X)
    (hu : ∀ R : L →ₗ[F] L, IsBracketCommuting R →
      ∃! ab : F × F, R = ab.1 • LinearMap.id + ab.2 • H) :
    IsBracketCommuting (t • H) ∧ (∀ X, (t • H) ((t • H) X) = (t ^ 2 * d) • X) ∧
      ∀ R : L →ₗ[F] L, IsBracketCommuting R →
        ∃! ab : F × F, R = ab.1 • LinearMap.id + ab.2 • (t • H) := by
  refine ⟨hc.smul t, ?_, ?_⟩
  · intro X
    rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, hsq, smul_smul, smul_smul]
    congr 1
    ring
  · intro R hR
    obtain ⟨⟨a, b⟩, hab, huniq⟩ := hu R hR
    dsimp only at hab
    refine ⟨(a, b / t), ?_, ?_⟩
    · dsimp only
      rw [smul_smul, div_mul_cancel₀ b ht]
      exact hab
    · rintro ⟨a', b'⟩ h'
      dsimp only at h'
      rw [smul_smul] at h'
      have h3 := huniq (a', b' * t) h'
      have h4 : a' = a := congrArg Prod.fst h3
      have h5 : b' * t = b := congrArg Prod.snd h3
      rw [h4, ← h5, mul_div_cancel_right₀ b' ht]

end FormCentroid

/-! ### D1M: the matrix form in dimension four -/

/-- **D1M (matrix form).** Let `F` be a field with `2 ≠ 0`, `ι` a finite index type with exactly
four elements, and `G` a symmetric `ι × ι` matrix over `F` with `det G ≠ 0`. Then, on the Lie
algebra of `G`-skew matrices, there is an `F`-linear endomorphism `H` such that: `H` is
bracket-commuting; `H (H X) = det G • X` for all `X`; and for every bracket-commuting `F`-linear
endomorphism `R` there is exactly one pair `(a, b)` in `F × F` with `R = a • id + b • H`. -/
theorem exists_hodge_matrix {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (h2 : (2 : F) ≠ 0) (hι : Fintype.card ι = 4) (G : Matrix ι ι F)
    (hG : G.IsSymm) (hdet : G.det ≠ 0) :
    ∃ H : skewAdjointMatricesLieSubalgebra G →ₗ[F] skewAdjointMatricesLieSubalgebra G,
      IsBracketCommuting H ∧ (∀ X, H (H X) = G.det • X) ∧
      ∀ R : skewAdjointMatricesLieSubalgebra G →ₗ[F] skewAdjointMatricesLieSubalgebra G,
        IsBracketCommuting R → ∃! ab : F × F, R = ab.1 • LinearMap.id + ab.2 • H := by
  obtain ⟨η, t, ht, hη, hprod, ⟨φ⟩⟩ :=
    FormCentroid.exists_lieEquiv_etaSkew h2 G hG hdet (Fintype.equivFinOfCardEq hι)
  obtain ⟨hc, hsq, hu⟩ := FormCentroid.hodge_description h2 η hη
  obtain ⟨H₁, hc₁, hsq₁, hu₁⟩ := centroid_transport_field φ (hodge η) _ hc hsq hu
  obtain ⟨hc₂, hsq₂, hu₂⟩ :=
    FormCentroid.description_smul H₁ _ t⁻¹ (inv_ne_zero ht) hc₁ hsq₁ hu₁
  refine ⟨t⁻¹ • H₁, hc₂, ?_, hu₂⟩
  intro X
  rw [hsq₂ X, hprod]
  congr 1
  field_simp

/-! ### From endomorphisms to matrices -/

namespace FormCentroid

/-- An endomorphism `f` is `B`-skew-adjoint exactly when its matrix in the basis `v` is skew for
the Gram matrix of `B` in `v`. -/
theorem toMatrix_mem_skew_iff {F V n : Type*} [Field F] [AddCommGroup V] [Module F V] [Fintype n]
    [DecidableEq n] (v : Module.Basis n F V) (B : LinearMap.BilinForm F V) (f : Module.End F V) :
    LinearMap.toMatrix v v f ∈
        skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix v B) ↔
      f ∈ skewAdjointLieSubalgebra B := by
  rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  have h := isAdjointPair_toLinearMap₂ v v (LinearMap.BilinForm.toMatrix v B)
    (LinearMap.BilinForm.toMatrix v B) (LinearMap.toMatrix v v f) (-(LinearMap.toMatrix v v f))
  have hB : Matrix.toLinearMap₂ v v (LinearMap.BilinForm.toMatrix v B) = B :=
    Matrix.toLinearMap₂_toMatrix₂ v v B
  rw [hB, map_neg, Matrix.toLin_toMatrix] at h
  change _ ↔ f ∈ B.skewAdjointSubmodule
  rw [LinearMap.mem_skewAdjointSubmodule]
  exact h.symm

/-- The Lie equivalence from the `B`-skew-adjoint endomorphisms to the skew matrices of the Gram
matrix of `B` in the basis `v`, `f ↦ LinearMap.toMatrix v v f`. -/
noncomputable def skewAdjointEquivMatrices {F V n : Type*} [Field F] [AddCommGroup V]
    [Module F V] [Fintype n] [DecidableEq n] (v : Module.Basis n F V)
    (B : LinearMap.BilinForm F V) :
    skewAdjointLieSubalgebra B ≃ₗ⁅F⁆
      skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix v B) :=
  LieEquiv.ofSubalgebras _ _ (LinearMap.toMatrixAlgEquiv v).toLieEquiv <| by
    ext M
    rw [LieSubalgebra.mem_map]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (toMatrix_mem_skew_iff v B f).mpr hf
    · intro hM
      refine ⟨Matrix.toLin v v M, ?_, ?_⟩
      · rw [← toMatrix_mem_skew_iff v B, LinearMap.toMatrix_toLin]
        exact hM
      · exact LinearMap.toMatrix_toLin v v M

/-- The Gram matrix of a symmetric bilinear form is a symmetric matrix. -/
theorem toMatrix_isSymm {F V n : Type*} [Field F] [AddCommGroup V] [Module F V] [Fintype n]
    [DecidableEq n] (v : Module.Basis n F V) (B : LinearMap.BilinForm F V) (hB : B.IsSymm) :
    (LinearMap.BilinForm.toMatrix v B).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rw [LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.toMatrix_apply]
  exact hB.eq _ _

end FormCentroid

/-! ### D1: a form on a vector space, in any basis -/

/-- **D1 (form on a vector space, for every basis).** Let `F` be a field with `2 ≠ 0`, `V` a
vector space over `F` with a basis `b` indexed by a finite type `ι` with exactly four elements, and
`B` a symmetric nondegenerate bilinear form on `V`. Write `d` for the determinant of the Gram matrix
of `B` in the basis `b`. Then, on the Lie algebra of the `B`-skew-adjoint endomorphisms of `V`,
there is an `F`-linear endomorphism `H` such that: `H` is bracket-commuting; `H (H X) = d • X` for
all `X`; and for every bracket-commuting `F`-linear endomorphism `R` there is exactly one pair
`(a, c)` in `F × F` with `R = a • id + c • H`. -/
theorem exists_hodge_of_basis {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype ι] [DecidableEq ι] (h2 : (2 : F) ≠ 0) (hι : Fintype.card ι = 4)
    (b : Module.Basis ι F V) (B : LinearMap.BilinForm F V) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) :
    ∃ H : skewAdjointLieSubalgebra B →ₗ[F] skewAdjointLieSubalgebra B,
      IsBracketCommuting H ∧
      (∀ X, H (H X) = (LinearMap.BilinForm.toMatrix b B).det • X) ∧
      ∀ R : skewAdjointLieSubalgebra B →ₗ[F] skewAdjointLieSubalgebra B, IsBracketCommuting R →
        ∃! ab : F × F, R = ab.1 • LinearMap.id + ab.2 • H := by
  have hdet : (LinearMap.BilinForm.toMatrix b B).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd
  obtain ⟨H, hc, hsq, hu⟩ := exists_hodge_matrix h2 hι (LinearMap.BilinForm.toMatrix b B)
    (FormCentroid.toMatrix_isSymm b B hB) hdet
  exact centroid_transport_field (FormCentroid.skewAdjointEquivMatrices b B) H _ hc hsq hu

/-! ### Consequences of a description by one operator -/

namespace FormCentroid

/-- If every bracket-commuting map is `a • id + b • H` for exactly one pair `(a, b)` and `H` is
bracket-commuting, then `a • id + b • H = a' • id + b' • H` implies `a = a'` and `b = b'`. -/
theorem pair_unique {F L : Type*} [Field F] [LieRing L] [LieAlgebra F L] (H : L →ₗ[F] L)
    (hc : IsBracketCommuting H)
    (hu : ∀ R : L →ₗ[F] L, IsBracketCommuting R →
      ∃! ab : F × F, R = ab.1 • LinearMap.id + ab.2 • H)
    (a b a' b' : F)
    (h : a • (LinearMap.id : L →ₗ[F] L) + b • H = a' • LinearMap.id + b' • H) :
    a = a' ∧ b = b' := by
  have hR : IsBracketCommuting (a • (LinearMap.id : L →ₗ[F] L) + b • H) :=
    (isBracketCommuting_id.smul a).add (hc.smul b)
  have h3 : ((a, b) : F × F) = (a', b') := (hu _ hR).unique rfl h
  exact ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩

/-- If `H` is bracket-commuting and every bracket-commuting map is `a • id + b • H` for exactly one
pair `(a, b)`, then `H` is not of the form `a • id`. -/
theorem not_scalar {F L : Type*} [Field F] [LieRing L] [LieAlgebra F L] (H : L →ₗ[F] L)
    (hc : IsBracketCommuting H)
    (hu : ∀ R : L →ₗ[F] L, IsBracketCommuting R →
      ∃! ab : F × F, R = ab.1 • LinearMap.id + ab.2 • H) :
    ¬ ∃ a : F, H = a • LinearMap.id := by
  rintro ⟨a, ha⟩
  have h : (a : F) • (LinearMap.id : L →ₗ[F] L) + (0 : F) • H =
      (0 : F) • LinearMap.id + (1 : F) • H := by
    rw [zero_smul, zero_smul, one_smul, add_zero, zero_add]
    exact ha.symm
  exact zero_ne_one (pair_unique H hc hu a 0 0 1 h).2

/-- If `H (H X) = d • X` for all `X` and `R = a • id + b • H`, then
`R (R X) = (a ^ 2 + b ^ 2 * d) • X + (2 * a * b) • H X`. -/
theorem sq_apply {F L : Type*} [Field F] [LieRing L] [LieAlgebra F L] (H : L →ₗ[F] L) (d : F)
    (hsq : ∀ X, H (H X) = d • X) (a b : F) (X : L) :
    (a • (LinearMap.id : L →ₗ[F] L) + b • H) ((a • (LinearMap.id : L →ₗ[F] L) + b • H) X) =
      (a ^ 2 + b ^ 2 * d) • X + (2 * a * b) • H X := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, map_add, map_smul,
    hsq]
  module

/-- If `2 ≠ 0`, `H` is bracket-commuting with `H (H X) = d • X`, every bracket-commuting map is
`a • id + b • H` for exactly one pair `(a, b)`, and `R` is bracket-commuting, not of the form
`a • id`, with `R (R X) = c • X`, then `R = t • H` and `c = t ^ 2 * d` for some `t ≠ 0`. -/
theorem eq_smul_of_nonscalar_sq {F L : Type*} [Field F] [LieRing L] [LieAlgebra F L]
    (h2 : (2 : F) ≠ 0) (H : L →ₗ[F] L) (d : F) (hc : IsBracketCommuting H)
    (hsq : ∀ X, H (H X) = d • X)
    (hu : ∀ R : L →ₗ[F] L, IsBracketCommuting R →
      ∃! ab : F × F, R = ab.1 • LinearMap.id + ab.2 • H)
    (c : F) (R : L →ₗ[F] L) (hR : IsBracketCommuting R) (hRs : ¬ ∃ a : F, R = a • LinearMap.id)
    (hR2 : ∀ X, R (R X) = c • X) : ∃ t : F, t ≠ 0 ∧ R = t • H ∧ c = t ^ 2 * d := by
  obtain ⟨⟨a, b⟩, hab, -⟩ := hu R hR
  dsimp only at hab
  have hb : b ≠ 0 := by
    intro hb
    apply hRs
    refine ⟨a, ?_⟩
    rw [hab, hb, zero_smul, add_zero]
  have h : (c : F) • (LinearMap.id : L →ₗ[F] L) + (0 : F) • H =
      (a ^ 2 + b ^ 2 * d) • LinearMap.id + (2 * a * b) • H := by
    ext X
    have h3 := hR2 X
    rw [hab, sq_apply H d hsq a b X] at h3
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, zero_smul, add_zero]
    exact h3.symm
  obtain ⟨h4, h5⟩ := pair_unique H hc hu _ _ _ _ h
  have ha : a = 0 := by
    rcases mul_eq_zero.mp h5.symm with h6 | h6
    · exact (mul_eq_zero.mp h6).resolve_left h2
    · exact absurd h6 hb
  refine ⟨b, hb, ?_, ?_⟩
  · rw [hab, ha, zero_smul, zero_add]
  · rw [h4, ha]
    ring

/-- If `2 ≠ 0`, `H` is bracket-commuting with `H (H X) = d • X`, and every bracket-commuting map
is `a • id + b • H` for exactly one pair `(a, b)`, then a bracket-commuting map `R` that is not of
the form `a • id` and has `R (R X) = c • X` exists if and only if `c = t ^ 2 * d` for some
`t ≠ 0`. -/
theorem exists_nonscalar_sq_iff_of_description {F L : Type*} [Field F] [LieRing L]
    [LieAlgebra F L] (h2 : (2 : F) ≠ 0) (H : L →ₗ[F] L) (d : F) (hc : IsBracketCommuting H)
    (hsq : ∀ X, H (H X) = d • X)
    (hu : ∀ R : L →ₗ[F] L, IsBracketCommuting R →
      ∃! ab : F × F, R = ab.1 • LinearMap.id + ab.2 • H) (c : F) :
    (∃ R : L →ₗ[F] L, IsBracketCommuting R ∧ (¬ ∃ a : F, R = a • LinearMap.id) ∧
        ∀ X, R (R X) = c • X) ↔
      ∃ t : F, t ≠ 0 ∧ c = t ^ 2 * d := by
  constructor
  · rintro ⟨R, hR, hRs, hR2⟩
    obtain ⟨t, ht, -, hct⟩ := eq_smul_of_nonscalar_sq h2 H d hc hsq hu c R hR hRs hR2
    exact ⟨t, ht, hct⟩
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨hc', hsq', hu'⟩ := description_smul H d t ht hc hsq hu
    exact ⟨t • H, hc', not_scalar (t • H) hc' hu', hsq'⟩

/-- If `2 ≠ 0`, `d ≠ 0`, `H₀` is bracket-commuting with `H₀ (H₀ X) = d • X`, and every
bracket-commuting map is `a • id + b • H₀` for exactly one pair `(a, b)`, then a bracket-commuting
`H` that is not of the form `a • id` and has `H (H X) = d • X` is `H₀` or `-H₀`. -/
theorem eq_or_eq_neg_of_description {F L : Type*} [Field F] [LieRing L] [LieAlgebra F L]
    (h2 : (2 : F) ≠ 0) (H₀ : L →ₗ[F] L) (d : F) (hd : d ≠ 0) (hc : IsBracketCommuting H₀)
    (hsq : ∀ X, H₀ (H₀ X) = d • X)
    (hu : ∀ R : L →ₗ[F] L, IsBracketCommuting R →
      ∃! ab : F × F, R = ab.1 • LinearMap.id + ab.2 • H₀)
    (H : L →ₗ[F] L) (hH : IsBracketCommuting H) (hHs : ¬ ∃ a : F, H = a • LinearMap.id)
    (hH2 : ∀ X, H (H X) = d • X) : H = H₀ ∨ H = -H₀ := by
  obtain ⟨t, -, hHt, hdt⟩ := eq_smul_of_nonscalar_sq h2 H₀ d hc hsq hu d H hH hHs hH2
  have h1 : (t - 1) * (t + 1) = 0 := by
    have h3 : ((t - 1) * (t + 1)) * d = 0 := by linear_combination -hdt
    exact (mul_eq_zero.mp h3).resolve_right hd
  rcases mul_eq_zero.mp h1 with h | h
  · left
    rw [hHt, sub_eq_zero.mp h, one_smul]
  · right
    rw [hHt, eq_neg_of_add_eq_zero_left h, neg_smul, one_smul]

/-- If `2 ≠ 0`, `d ≠ 0`, `H` is bracket-commuting with `H (H X) = d • X`, and every
bracket-commuting map is `a • id + b • H` for exactly one pair `(a, b)`, then a bracket-commuting
map `R` with `R (R X) = -X` exists if and only if `-d` is a square or `-1` is a square. -/
theorem exists_sq_neg_one_iff_of_description {F L : Type*} [Field F] [LieRing L]
    [LieAlgebra F L] (h2 : (2 : F) ≠ 0) (H : L →ₗ[F] L) (d : F) (hd : d ≠ 0)
    (hc : IsBracketCommuting H) (hsq : ∀ X, H (H X) = d • X)
    (hu : ∀ R : L →ₗ[F] L, IsBracketCommuting R →
      ∃! ab : F × F, R = ab.1 • LinearMap.id + ab.2 • H) :
    (∃ R : L →ₗ[F] L, IsBracketCommuting R ∧ ∀ X, R (R X) = -X) ↔
      IsSquare (-d) ∨ IsSquare (-1 : F) := by
  constructor
  · rintro ⟨R, hR, hR2⟩
    by_cases hRs : ∃ a : F, R = a • LinearMap.id
    · right
      obtain ⟨a, rfl⟩ := hRs
      have h : (a * a) • (LinearMap.id : L →ₗ[F] L) + (0 : F) • H =
          (-1 : F) • LinearMap.id + (0 : F) • H := by
        ext X
        have h3 := hR2 X
        simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul] at h3
        simp only [LinearMap.smul_apply, LinearMap.id_apply, zero_smul, add_zero, neg_smul,
          one_smul]
        exact h3
      exact ⟨a, (pair_unique H hc hu _ _ _ _ h).1.symm⟩
    · left
      have hR2' : ∀ X, R (R X) = (-1 : F) • X := fun X => by rw [hR2 X, neg_smul, one_smul]
      obtain ⟨t, ht, -, hct⟩ := eq_smul_of_nonscalar_sq h2 H d hc hsq hu (-1) R hR hRs hR2'
      refine ⟨t⁻¹, ?_⟩
      have h4 : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
      linear_combination (t⁻¹ * t⁻¹) * hct + (d * (1 + t * t⁻¹)) * h4
  · rintro (⟨r, hr⟩ | ⟨r, hr⟩)
    · have hr0 : r ≠ 0 := by
        rintro rfl
        apply hd
        rw [mul_zero, neg_eq_zero] at hr
        exact hr
      obtain ⟨hc', hsq', -⟩ := description_smul H d r⁻¹ (inv_ne_zero hr0) hc hsq hu
      refine ⟨r⁻¹ • H, hc', fun X => ?_⟩
      rw [hsq' X]
      have h4 : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0
      have h5 : r⁻¹ ^ 2 * d = -1 := by
        linear_combination (-(r⁻¹ ^ 2)) * hr + (-(1 + r * r⁻¹)) * h4
      rw [h5, neg_smul, one_smul]
    · refine ⟨r • LinearMap.id, isBracketCommuting_id.smul r, fun X => ?_⟩
      simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
      rw [← hr, neg_smul, one_smul]

end FormCentroid

/-! ### D1 (sign) and D1′: squares, and the square class of the Gram determinant -/

/-- **D1 (uniqueness up to sign).** With `F`, `V`, `b`, `ι`, `B` as in D1 and `d` the determinant
of the Gram matrix of `B` in the basis `b`: if `H` and `H'` are `F`-linear endomorphisms of the Lie
algebra of the `B`-skew-adjoint endomorphisms, each bracket-commuting, each not of the form
`a • id`, and each with `H (H X) = d • X`, `H' (H' X) = d • X` for all `X`, then `H' = H` or
`H' = -H`. -/
theorem hodge_of_basis_eq_or_eq_neg {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype ι] [DecidableEq ι] (h2 : (2 : F) ≠ 0) (hι : Fintype.card ι = 4)
    (b : Module.Basis ι F V) (B : LinearMap.BilinForm F V) (hB : B.IsSymm)
    (hnd : B.Nondegenerate)
    (H H' : skewAdjointLieSubalgebra B →ₗ[F] skewAdjointLieSubalgebra B)
    (hH : IsBracketCommuting H) (hHs : ¬ ∃ a : F, H = a • LinearMap.id)
    (hH2 : ∀ X, H (H X) = (LinearMap.BilinForm.toMatrix b B).det • X)
    (hH' : IsBracketCommuting H') (hH's : ¬ ∃ a : F, H' = a • LinearMap.id)
    (hH'2 : ∀ X, H' (H' X) = (LinearMap.BilinForm.toMatrix b B).det • X) :
    H' = H ∨ H' = -H := by
  have hdet : (LinearMap.BilinForm.toMatrix b B).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd
  obtain ⟨H₀, hc, hsq, hu⟩ := exists_hodge_of_basis h2 hι b B hB hnd
  rcases FormCentroid.eq_or_eq_neg_of_description h2 H₀ _ hdet hc hsq hu H hH hHs hH2 with
    h | h <;>
  rcases FormCentroid.eq_or_eq_neg_of_description h2 H₀ _ hdet hc hsq hu H' hH' hH's hH'2 with
    h' | h'
  · left
    rw [h, h']
  · right
    rw [h, h']
  · right
    rw [h, h', neg_neg]
  · left
    rw [h, h']

/-- **D1′ (the squares of the non-scalar bracket-commuting maps).** With `F`, `V`, `b`, `ι`, `B`
as in D1, `d` the determinant of the Gram matrix of `B` in the basis `b`, and `c` in `F`: there is
a bracket-commuting `F`-linear endomorphism `R` of the Lie algebra of the `B`-skew-adjoint
endomorphisms that is not of the form `a • id` and satisfies `R (R X) = c • X` for all `X`, if and
only if there is `t ≠ 0` in `F` with `c = t ^ 2 * d`. -/
theorem exists_nonscalar_sq_iff {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype ι] [DecidableEq ι] (h2 : (2 : F) ≠ 0) (hι : Fintype.card ι = 4)
    (b : Module.Basis ι F V) (B : LinearMap.BilinForm F V) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) (c : F) :
    (∃ R : skewAdjointLieSubalgebra B →ₗ[F] skewAdjointLieSubalgebra B,
        IsBracketCommuting R ∧ (¬ ∃ a : F, R = a • LinearMap.id) ∧ ∀ X, R (R X) = c • X) ↔
      ∃ t : F, t ≠ 0 ∧ c = t ^ 2 * (LinearMap.BilinForm.toMatrix b B).det := by
  obtain ⟨H₀, hc, hsq, hu⟩ := exists_hodge_of_basis h2 hι b B hB hnd
  exact FormCentroid.exists_nonscalar_sq_iff_of_description h2 H₀ _ hc hsq hu c

/-- **D1′ (square `-1`).** With `F`, `V`, `b`, `ι`, `B` as in D1 and `d` the determinant of the
Gram matrix of `B` in the basis `b`: there is a bracket-commuting `F`-linear endomorphism `R` of the
Lie algebra of the `B`-skew-adjoint endomorphisms with `R (R X) = -X` for all `X`, if and only if
`-d` is a square in `F` or `-1` is a square in `F`. (The second alternative is the scalar case
`R = a • id` with `a ^ 2 = -1`.) -/
theorem exists_sq_neg_one_iff {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype ι] [DecidableEq ι] (h2 : (2 : F) ≠ 0) (hι : Fintype.card ι = 4)
    (b : Module.Basis ι F V) (B : LinearMap.BilinForm F V) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) :
    (∃ R : skewAdjointLieSubalgebra B →ₗ[F] skewAdjointLieSubalgebra B,
        IsBracketCommuting R ∧ ∀ X, R (R X) = -X) ↔
      IsSquare (-(LinearMap.BilinForm.toMatrix b B).det) ∨ IsSquare (-1 : F) := by
  have hdet : (LinearMap.BilinForm.toMatrix b B).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd
  obtain ⟨H₀, hc, hsq, hu⟩ := exists_hodge_of_basis h2 hι b B hB hnd
  exact FormCentroid.exists_sq_neg_one_iff_of_description h2 H₀ _ hdet hc hsq hu

/-- **D1′ (the square class of the Gram determinant is determined by the Lie algebra).** Let `F` be
a field with `2 ≠ 0`. Let `V` and `V'` be vector spaces over `F` with bases `b` and `b'` indexed by
finite types `ι` and `ι'` with exactly four elements each, and let `B` on `V` and `B'` on `V'` be
symmetric nondegenerate bilinear forms. If there is a Lie algebra equivalence from the Lie algebra
of the `B`-skew-adjoint endomorphisms of `V` to that of the `B'`-skew-adjoint endomorphisms of `V'`,
then there is `t ≠ 0` in `F` such that the determinant of the Gram matrix of `B'` in `b'` is `t ^ 2`
times the determinant of the Gram matrix of `B` in `b`. -/
theorem det_toMatrix_eq_sq_mul_of_lieEquiv {F V ι : Type*} [Field F] [AddCommGroup V]
    [Module F V] [Fintype ι] [DecidableEq ι] {V' ι' : Type*} [AddCommGroup V'] [Module F V']
    [Fintype ι'] [DecidableEq ι'] (h2 : (2 : F) ≠ 0) (hι : Fintype.card ι = 4)
    (hι' : Fintype.card ι' = 4)
    (b : Module.Basis ι F V) (b' : Module.Basis ι' F V')
    (B : LinearMap.BilinForm F V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (B' : LinearMap.BilinForm F V') (hB' : B'.IsSymm) (hnd' : B'.Nondegenerate)
    (e : skewAdjointLieSubalgebra B ≃ₗ⁅F⁆ skewAdjointLieSubalgebra B') :
    ∃ t : F, t ≠ 0 ∧
      (LinearMap.BilinForm.toMatrix b' B').det =
        t ^ 2 * (LinearMap.BilinForm.toMatrix b B).det := by
  obtain ⟨H', hc', hsq', hu'⟩ := exists_hodge_of_basis h2 hι' b' B' hB' hnd'
  refine (exists_nonscalar_sq_iff h2 hι b B hB hnd _).mp
    ⟨(e.symm.toLinearEquiv : skewAdjointLieSubalgebra B' →ₗ[F] skewAdjointLieSubalgebra B) ∘ₗ
        H' ∘ₗ (e.toLinearEquiv : skewAdjointLieSubalgebra B →ₗ[F] skewAdjointLieSubalgebra B'),
      hc'.lieEquivConj e.symm, ?_, ?_⟩
  · rintro ⟨a, ha⟩
    apply FormCentroid.not_scalar H' hc' hu'
    refine ⟨a, LinearMap.ext fun Y => ?_⟩
    have h1 := LinearMap.congr_fun ha (e.symm Y)
    change e.symm (H' (e (e.symm Y))) = a • e.symm Y at h1
    rw [LieEquiv.apply_symm_apply, ← map_smul] at h1
    exact e.symm.injective h1
  · intro X
    change e.symm (H' (e (e.symm (H' (e X))))) = _ • X
    rw [LieEquiv.apply_symm_apply, hsq', map_smul, LieEquiv.symm_apply_apply]

/-! ### D5(a): every other finite dimension -/

/-- **D5(a) (control: the number four).** Let `F` be a field with `2 ≠ 0`, `V` a vector space over
`F` with a basis `b` indexed by a finite type `ι` whose number of elements is not four, and `B` a
symmetric nondegenerate bilinear form on `V`. Then every bracket-commuting `F`-linear endomorphism
`R` of the Lie algebra of the `B`-skew-adjoint endomorphisms of `V` is of the form `c • id` with `c`
in `F`. -/
theorem centroid_scalar_of_basis {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype ι] (h2 : (2 : F) ≠ 0) (hι : Fintype.card ι ≠ 4)
    (b : Module.Basis ι F V) (B : LinearMap.BilinForm F V) (hB : B.IsSymm)
    (hnd : B.Nondegenerate)
    (R : skewAdjointLieSubalgebra B →ₗ[F] skewAdjointLieSubalgebra B)
    (hR : IsBracketCommuting R) : ∃ c : F, R = c • LinearMap.id := by
  classical
  have hdet : (LinearMap.BilinForm.toMatrix b B).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd
  obtain ⟨η, -, -, hη, -, ⟨φ⟩⟩ := FormCentroid.exists_lieEquiv_etaSkew h2
    (LinearMap.BilinForm.toMatrix b B) (FormCentroid.toMatrix_isSymm b B hB) hdet (Equiv.refl ι)
  have ψ : skewAdjointLieSubalgebra B ≃ₗ⁅F⁆ etaSkew η :=
    (FormCentroid.skewAdjointEquivMatrices b B).trans φ
  obtain ⟨c, hc⟩ := centroid_scalar_of_two_ne_zero h2 hι η hη _ (hR.lieEquivConj ψ)
  refine ⟨c, LinearMap.ext fun X => ?_⟩
  have h1 := LinearMap.congr_fun hc (ψ X)
  change ψ (R (ψ.symm (ψ X))) = c • ψ X at h1
  rw [LieEquiv.symm_apply_apply, ← map_smul] at h1
  exact ψ.injective h1

end LorentzLie
