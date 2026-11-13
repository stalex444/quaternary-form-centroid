module
public import Mathlib
public import LorentzLie.Defs
public import LorentzLie.FormDefs
public import LorentzLie.FormCentroid
public import HermiteCompositum.Assembly

@[expose] public section

/-!
# Bracket-commuting maps on the trace-form Lie algebra of a number field of degree four

Bracket-commuting means `∀ X Y, R ⁅X, Y⁆ = ⁅X, R Y⁆` (`LorentzLie.IsBracketCommuting`).
For a number field `K`, the Lie algebra here is the Lie algebra over `ℚ` of the `ℚ`-linear
endomorphisms of `K` that are skew-adjoint for the trace form `(x, y) ↦ Tr_{K/ℚ}(x * y)`
(`skewAdjointLieSubalgebra (Algebra.traceForm ℚ K)`). `NumberField.discr K` is Mathlib's
discriminant of `K`, an integer.

Statements for a number field `K`. Each is proved from the statements of `LorentzLie.FormCentroid`
applied to the trace form of `K`, or to its Gram matrix read in `ℝ`, in Mathlib's integral basis;
the determinant of that Gram matrix is `NumberField.discr K`. The third and the fifth also use that
`-1` and `283` are not squares of rational numbers, and the last uses `NumberField.sign_discr`.

* `exists_hodge_traceForm`: if `K` has degree four, there is a bracket-commuting `H` with
  `H (H X) = (NumberField.discr K : ℚ) • X`, and every bracket-commuting map is
  `a • id + b • H` for exactly one pair `(a, b)` of rational numbers.
* `exists_nonscalar_sq_iff_traceForm`: if `K` has degree four, a bracket-commuting map that is not
  of the form `a • id` and has `R (R X) = c • X` exists if and only if `c = t ^ 2 * discr K` for
  some rational `t ≠ 0`.
* `exists_sq_neg_one_iff_traceForm`: if `K` has degree four, a bracket-commuting map with
  `R (R X) = -X` exists if and only if `-discr K` is the square of a rational number.
* `centroid_scalar_traceForm`: if the degree of `K` is not four, every bracket-commuting map is
  `c • id`.
* `not_exists_sq_neg_one_of_discr_eq`: degree four and `discr K = -283` exclude a bracket-commuting
  map with `R (R X) = -X`.
* `exists_hodge_traceMatrix_real`: if `K` has degree four, then on the Lie algebra over `ℝ` of the
  matrices skew for the real trace matrix of the integral basis there is a bracket-commuting `H`
  with `H (H X) = (-1) ^ r₂ • X`, `r₂` the number of complex places of `K`, and every
  bracket-commuting map is `a • id + b • H` for exactly one pair `(a, b)` of real numbers.

Statements for the explicit matrix `traceGram` (`LorentzLie.FormDefs`; determinant `-283`):
`traceGram_hodge_rat`, `traceGram_not_exists_sq_neg_one_rat` (over `ℚ`),
`traceGram_exists_sq_neg_one_real` (over `ℝ`).

Statements for the field `S₄ = ℚ⟮Q⟯` of `HermiteCompositum.Instance` (degree four, discriminant
`-283`), with no hypothesis: `exists_hodge_traceForm_S₄`, `not_exists_sq_neg_one_S₄`,
`exists_nonscalar_sq_iff_S₄`.

Controls: `diag_exists_sq_neg_one_rat` (the diagonal matrix with diagonal `(1, 1, 1, -1)` over
`ℚ`: a bracket-commuting map with `R (R X) = -X` exists), `scalar_sq_control_S₄` (the clause
"not of the form `a • id`" of `exists_nonscalar_sq_iff_S₄` cannot be deleted) and
`diag_degenerate_centroid_scalar` (for the diagonal matrix with diagonal `(1, 1, 1, 0)` over `ℚ`,
of determinant `0`, every bracket-commuting map is `c • id`).

The helper lemmas are in the namespace `LorentzLie.QuarticField`: the arithmetic facts
(`not_isSquare_neg_one_rat`, `not_isSquare_283_rat`), the integral basis
(`det_toMatrix_integralBasis`, `card_integralBasis_index`), the real trace matrix
(`traceMatrix_real_isSymm`, `traceMatrix_real_det`, `discr_eq_neg_one_pow_mul_abs`,
`inv_sqrt_abs_discr_sq_mul_discr`), and, for the last control, the matrices `degMat a b c p q r d`
with rows `(0, a, b, 0)`, `(-a, 0, c, 0)`, `(-b, -c, 0, 0)`, `(p, q, r, d)`, which are exactly the
matrices skew for the diagonal matrix with diagonal `(1, 1, 1, 0)` (`degMat_mem`,
`coe_eq_degMat`).
-/

set_option autoImplicit false

attribute [local instance] LieRing.ofAssociativeRing

namespace LorentzLie

namespace QuarticField

/-- `-1` is not the square of a rational number. -/
theorem not_isSquare_neg_one_rat : ¬ IsSquare (-1 : ℚ) := by
  rintro ⟨r, hr⟩
  nlinarith [mul_self_nonneg r]

/-- `283` is not the square of a rational number. -/
theorem not_isSquare_283_rat : ¬ IsSquare (283 : ℚ) := by
  rw [show (283 : ℚ) = ((283 : ℕ) : ℚ) by norm_num, Rat.isSquare_natCast_iff]
  rintro ⟨r, hr⟩
  have h1 : r < 17 := by nlinarith
  interval_cases r <;> omega

/-- For a number field `K`, the determinant of the Gram matrix of the trace form of `K` over `ℚ`
in Mathlib's integral basis `NumberField.integralBasis K` is `NumberField.discr K`, read in `ℚ`. -/
theorem det_toMatrix_integralBasis (K : Type*) [Field K] [NumberField K] :
    (LinearMap.BilinForm.toMatrix (NumberField.integralBasis K) (Algebra.traceForm ℚ K)).det =
      (NumberField.discr K : ℚ) := by
  rw [NumberField.coe_discr, Algebra.discr_def, Algebra.traceMatrix_of_basis]

/-- For a number field `K`, the index type of Mathlib's integral basis has `Module.finrank ℚ K`
elements. -/
theorem card_integralBasis_index (K : Type*) [Field K] [NumberField K] :
    Fintype.card (Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)) =
      Module.finrank ℚ K :=
  (Module.finrank_eq_card_basis (NumberField.integralBasis K)).symm

end QuarticField

/-- **D2 (number fields of degree four).** Let `K` be a number field of degree four over `ℚ`. On
the Lie algebra over `ℚ` of the `ℚ`-linear endomorphisms of `K` that are skew-adjoint for the trace
form `(x, y) ↦ Tr_{K/ℚ}(x * y)`, there is a `ℚ`-linear endomorphism `H` such that: `H` is
bracket-commuting; `H (H X) = d_K • X` for all `X`, where `d_K` is the discriminant of `K`
(Mathlib's `NumberField.discr K`, an integer, read in `ℚ`); and for every bracket-commuting
`ℚ`-linear endomorphism `R` there is exactly one pair `(a, b)` in `ℚ × ℚ` with
`R = a • id + b • H`. -/
theorem exists_hodge_traceForm (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 4) :
    ∃ H : skewAdjointLieSubalgebra (Algebra.traceForm ℚ K) →ₗ[ℚ]
        skewAdjointLieSubalgebra (Algebra.traceForm ℚ K),
      IsBracketCommuting H ∧ (∀ X, H (H X) = (NumberField.discr K : ℚ) • X) ∧
      ∀ R : skewAdjointLieSubalgebra (Algebra.traceForm ℚ K) →ₗ[ℚ]
          skewAdjointLieSubalgebra (Algebra.traceForm ℚ K), IsBracketCommuting R →
        ∃! ab : ℚ × ℚ, R = ab.1 • LinearMap.id + ab.2 • H := by
  have h := exists_hodge_of_basis (by norm_num : (2 : ℚ) ≠ 0)
    ((QuarticField.card_integralBasis_index K).trans hK) (NumberField.integralBasis K)
    (Algebra.traceForm ℚ K) (Algebra.traceForm_isSymm ℚ) (traceForm_nondegenerate ℚ K)
  rw [QuarticField.det_toMatrix_integralBasis] at h
  exact h

/-- **D2 (the squares of the non-scalar bracket-commuting maps).** Let `K` be a number field of
degree four over `ℚ`, with discriminant `d_K`, and let `c` be a rational number. There is a
bracket-commuting `ℚ`-linear endomorphism `R` of the Lie algebra of the trace-form-skew-adjoint
endomorphisms of `K` that is not of the form `a • id` and satisfies `R (R X) = c • X` for all `X`,
if and only if there is a rational `t ≠ 0` with `c = t ^ 2 * d_K`. -/
theorem exists_nonscalar_sq_iff_traceForm (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 4) (c : ℚ) :
    (∃ R : skewAdjointLieSubalgebra (Algebra.traceForm ℚ K) →ₗ[ℚ]
          skewAdjointLieSubalgebra (Algebra.traceForm ℚ K),
        IsBracketCommuting R ∧ (¬ ∃ a : ℚ, R = a • LinearMap.id) ∧ ∀ X, R (R X) = c • X) ↔
      ∃ t : ℚ, t ≠ 0 ∧ c = t ^ 2 * (NumberField.discr K : ℚ) := by
  have h := exists_nonscalar_sq_iff (by norm_num : (2 : ℚ) ≠ 0)
    ((QuarticField.card_integralBasis_index K).trans hK) (NumberField.integralBasis K)
    (Algebra.traceForm ℚ K) (Algebra.traceForm_isSymm ℚ) (traceForm_nondegenerate ℚ K) c
  rw [QuarticField.det_toMatrix_integralBasis] at h
  exact h

/-- **D2 (square `-1`).** Let `K` be a number field of degree four over `ℚ`, with discriminant
`d_K`. There is a bracket-commuting `ℚ`-linear endomorphism `R` of the Lie algebra of the
trace-form-skew-adjoint endomorphisms of `K` with `R (R X) = -X` for all `X`, if and only if
`-d_K` is the square of a rational number. -/
theorem exists_sq_neg_one_iff_traceForm (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 4) :
    (∃ R : skewAdjointLieSubalgebra (Algebra.traceForm ℚ K) →ₗ[ℚ]
          skewAdjointLieSubalgebra (Algebra.traceForm ℚ K),
        IsBracketCommuting R ∧ ∀ X, R (R X) = -X) ↔
      IsSquare (-(NumberField.discr K : ℚ)) := by
  have h := exists_sq_neg_one_iff (by norm_num : (2 : ℚ) ≠ 0)
    ((QuarticField.card_integralBasis_index K).trans hK) (NumberField.integralBasis K)
    (Algebra.traceForm ℚ K) (Algebra.traceForm_isSymm ℚ) (traceForm_nondegenerate ℚ K)
  rw [QuarticField.det_toMatrix_integralBasis] at h
  rw [h]
  exact or_iff_left QuarticField.not_isSquare_neg_one_rat

/-- **D5(a) for a number field (control: degree four).** Let `K` be a number field whose degree
over `ℚ` is not four. Then every bracket-commuting `ℚ`-linear endomorphism `R` of the Lie algebra of
the trace-form-skew-adjoint endomorphisms of `K` is of the form `c • id` with `c` rational. -/
theorem centroid_scalar_traceForm (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K ≠ 4)
    (R : skewAdjointLieSubalgebra (Algebra.traceForm ℚ K) →ₗ[ℚ]
      skewAdjointLieSubalgebra (Algebra.traceForm ℚ K)) (hR : IsBracketCommuting R) :
    ∃ c : ℚ, R = c • LinearMap.id := by
  exact centroid_scalar_of_basis (by norm_num : (2 : ℚ) ≠ 0)
    (by rw [QuarticField.card_integralBasis_index K]; exact hK) (NumberField.integralBasis K)
    (Algebra.traceForm ℚ K) (Algebra.traceForm_isSymm ℚ) (traceForm_nondegenerate ℚ K) R hR

/-- **D3 (hypothesis form).** Let `K` be a number field of degree four over `ℚ` with discriminant
`-283`. Then no bracket-commuting `ℚ`-linear endomorphism `R` of the Lie algebra of the
trace-form-skew-adjoint endomorphisms of `K` satisfies `R (R X) = -X` for all `X`. -/
theorem not_exists_sq_neg_one_of_discr_eq (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 4) (hd : NumberField.discr K = -283) :
    ¬ ∃ R : skewAdjointLieSubalgebra (Algebra.traceForm ℚ K) →ₗ[ℚ]
          skewAdjointLieSubalgebra (Algebra.traceForm ℚ K),
        IsBracketCommuting R ∧ ∀ X, R (R X) = -X := by
  rw [exists_sq_neg_one_iff_traceForm K hK, hd]
  have hc : (-((-283 : ℤ) : ℚ)) = 283 := by norm_num
  rw [hc]
  exact QuarticField.not_isSquare_283_rat

/-- **D3 (matrix form, over `ℚ`).** Let `G = traceGram ℚ` be the rational symmetric matrix with rows
`(4, 0, 0, 3)`, `(0, 0, 3, 4)`, `(0, 3, 4, 0)`, `(3, 4, 0, 3)` (determinant `-283`; it is the Gram
matrix of the trace form of `ℚ⟮Q⟯`, `Q ^ 4 = Q + 1`, on `1, Q, Q², Q³`, by
`traceGram_eq_traceForm`). On the Lie algebra over `ℚ` of the `G`-skew matrices there is a
`ℚ`-linear endomorphism `H` such that: `H` is bracket-commuting; `H (H X) = (-283) • X` for all `X`;
and for every bracket-commuting `ℚ`-linear endomorphism `R` there is exactly one pair `(a, b)` in
`ℚ × ℚ` with `R = a • id + b • H`. -/
theorem traceGram_hodge_rat :
    ∃ H : skewAdjointMatricesLieSubalgebra (traceGram ℚ) →ₗ[ℚ]
        skewAdjointMatricesLieSubalgebra (traceGram ℚ),
      IsBracketCommuting H ∧ (∀ X, H (H X) = (-283 : ℚ) • X) ∧
      ∀ R : skewAdjointMatricesLieSubalgebra (traceGram ℚ) →ₗ[ℚ]
          skewAdjointMatricesLieSubalgebra (traceGram ℚ), IsBracketCommuting R →
        ∃! ab : ℚ × ℚ, R = ab.1 • LinearMap.id + ab.2 • H := by
  have h := exists_hodge_matrix (by norm_num : (2 : ℚ) ≠ 0) (by simp) (traceGram ℚ)
    (traceGram_isSymm ℚ) (by rw [traceGram_det]; norm_num)
  rw [traceGram_det] at h
  exact h

/-- **D3 (matrix form, over `ℚ`: no square `-1`).** On the Lie algebra over `ℚ` of the
`traceGram ℚ`-skew matrices, no bracket-commuting `ℚ`-linear endomorphism `R` satisfies
`R (R X) = -X` for all `X`. -/
theorem traceGram_not_exists_sq_neg_one_rat :
    ¬ ∃ R : skewAdjointMatricesLieSubalgebra (traceGram ℚ) →ₗ[ℚ]
          skewAdjointMatricesLieSubalgebra (traceGram ℚ),
        IsBracketCommuting R ∧ ∀ X, R (R X) = -X := by
  obtain ⟨H, hc, hsq, hu⟩ := traceGram_hodge_rat
  intro h
  have h3 := (FormCentroid.exists_sq_neg_one_iff_of_description (by norm_num : (2 : ℚ) ≠ 0) H
    (-283) (by norm_num) hc hsq hu).mp h
  rw [neg_neg] at h3
  rcases h3 with h3 | h3
  · exact QuarticField.not_isSquare_283_rat h3
  · exact QuarticField.not_isSquare_neg_one_rat h3

/-- **D3 (matrix form, over `ℝ`: a square `-1`).** On the Lie algebra over `ℝ` of the
`traceGram ℝ`-skew matrices (the same matrix, with real entries: `traceGram_rat_map_real`), there is
a bracket-commuting `ℝ`-linear endomorphism `R` with `R (R X) = -X` for all `X`. -/
theorem traceGram_exists_sq_neg_one_real :
    ∃ R : skewAdjointMatricesLieSubalgebra (traceGram ℝ) →ₗ[ℝ]
          skewAdjointMatricesLieSubalgebra (traceGram ℝ),
        IsBracketCommuting R ∧ ∀ X, R (R X) = -X := by
  obtain ⟨H, hc, hsq, hu⟩ := exists_hodge_matrix (by norm_num : (2 : ℝ) ≠ 0) (by simp)
    (traceGram ℝ) (traceGram_isSymm ℝ) (by rw [traceGram_det]; norm_num)
  rw [traceGram_det] at hsq
  refine (FormCentroid.exists_sq_neg_one_iff_of_description (by norm_num : (2 : ℝ) ≠ 0) H
    (-283) (by norm_num) hc hsq hu).mpr (Or.inl ⟨Real.sqrt 283, ?_⟩)
  rw [neg_neg, Real.mul_self_sqrt (by norm_num)]

/-- **The instance at `S₄ = ℚ⟮Q⟯` (existence and the description).** Let `S₄` be the field
`ℚ⟮Q⟯` of `HermiteCompositum.Instance`, `Q` a root of `x⁴ - x - 1`. On the Lie algebra over `ℚ` of
the `ℚ`-linear endomorphisms of `S₄` that are skew-adjoint for the trace form of `S₄` over `ℚ`,
there is a `ℚ`-linear endomorphism `H` such that: `H` is bracket-commuting; `H (H X) = (-283) • X`
for all `X`; and for every bracket-commuting `ℚ`-linear endomorphism `R` there is exactly one pair
`(a, b)` in `ℚ × ℚ` with `R = a • id + b • H`. No hypothesis. -/
theorem exists_hodge_traceForm_S₄ :
    ∃ H : skewAdjointLieSubalgebra (Algebra.traceForm ℚ HermiteCompositum.Instance.S₄) →ₗ[ℚ]
        skewAdjointLieSubalgebra (Algebra.traceForm ℚ HermiteCompositum.Instance.S₄),
      IsBracketCommuting H ∧ (∀ X, H (H X) = (-283 : ℚ) • X) ∧
      ∀ R : skewAdjointLieSubalgebra (Algebra.traceForm ℚ HermiteCompositum.Instance.S₄) →ₗ[ℚ]
          skewAdjointLieSubalgebra (Algebra.traceForm ℚ HermiteCompositum.Instance.S₄),
        IsBracketCommuting R → ∃! ab : ℚ × ℚ, R = ab.1 • LinearMap.id + ab.2 • H := by
  have h := exists_hodge_traceForm HermiteCompositum.Instance.S₄
    HermiteCompositum.Instance.finrank_S₄
  rw [HermiteCompositum.Instance.discr_S₄] at h
  have hc : ((-283 : ℤ) : ℚ) = -283 := by norm_num
  rw [hc] at h
  exact h

/-- **The instance at `S₄ = ℚ⟮Q⟯` (no square `-1` over `ℚ`).** No bracket-commuting `ℚ`-linear
endomorphism `R` of the Lie algebra of the trace-form-skew-adjoint endomorphisms of `S₄` satisfies
`R (R X) = -X` for all `X`. No hypothesis. -/
theorem not_exists_sq_neg_one_S₄ :
    ¬ ∃ R : skewAdjointLieSubalgebra (Algebra.traceForm ℚ HermiteCompositum.Instance.S₄) →ₗ[ℚ]
          skewAdjointLieSubalgebra (Algebra.traceForm ℚ HermiteCompositum.Instance.S₄),
        IsBracketCommuting R ∧ ∀ X, R (R X) = -X := by
  exact not_exists_sq_neg_one_of_discr_eq HermiteCompositum.Instance.S₄
    HermiteCompositum.Instance.finrank_S₄ HermiteCompositum.Instance.discr_S₄

/-- **The instance at `S₄ = ℚ⟮Q⟯` (the squares of the non-scalar bracket-commuting maps).** Let `c`
be a rational number. There is a bracket-commuting `ℚ`-linear endomorphism `R` of the Lie algebra of
the trace-form-skew-adjoint endomorphisms of `S₄` that is not of the form `a • id` and satisfies
`R (R X) = c • X` for all `X`, if and only if there is a rational `t ≠ 0` with
`c = t ^ 2 * (-283)`. No hypothesis. -/
theorem exists_nonscalar_sq_iff_S₄ (c : ℚ) :
    (∃ R : skewAdjointLieSubalgebra (Algebra.traceForm ℚ HermiteCompositum.Instance.S₄) →ₗ[ℚ]
          skewAdjointLieSubalgebra (Algebra.traceForm ℚ HermiteCompositum.Instance.S₄),
        IsBracketCommuting R ∧ (¬ ∃ a : ℚ, R = a • LinearMap.id) ∧ ∀ X, R (R X) = c • X) ↔
      ∃ t : ℚ, t ≠ 0 ∧ c = t ^ 2 * (-283) := by
  have h := exists_nonscalar_sq_iff_traceForm HermiteCompositum.Instance.S₄
    HermiteCompositum.Instance.finrank_S₄ c
  rw [HermiteCompositum.Instance.discr_S₄] at h
  have hc : ((-283 : ℤ) : ℚ) = -283 := by norm_num
  rw [hc] at h
  exact h

/-- **Control for `traceGram_not_exists_sq_neg_one_rat` (a rational symmetric matrix with negative
determinant for which a square `-1` exists).** On the Lie algebra over `ℚ` of the rational matrices
skew for the diagonal matrix with diagonal `(1, 1, 1, -1)` (determinant `-1`), there is a
bracket-commuting `ℚ`-linear endomorphism `R` with `R (R X) = -X` for all `X`. -/
theorem diag_exists_sq_neg_one_rat :
    ∃ R : skewAdjointMatricesLieSubalgebra
          (Matrix.diagonal ![1, 1, 1, -1] : Matrix (Fin 4) (Fin 4) ℚ) →ₗ[ℚ]
        skewAdjointMatricesLieSubalgebra
          (Matrix.diagonal ![1, 1, 1, -1] : Matrix (Fin 4) (Fin 4) ℚ),
      IsBracketCommuting R ∧ ∀ X, R (R X) = -X := by
  have hη : ∀ i, (![1, 1, 1, -1] : Fin 4 → ℚ) i ≠ 0 := by
    intro i; fin_cases i <;> norm_num
  refine ⟨hodge (![1, 1, 1, -1] : Fin 4 → ℚ), fun X Y => hodge_lie (by norm_num) _ hη X Y,
    fun X => ?_⟩
  rw [hodge_hodge (by norm_num) _ hη X]
  simp [Fin.prod_univ_four]

namespace QuarticField

/-- For a number field `K`, the real matrix obtained from the trace matrix of Mathlib's integral
basis by reading its rational entries in `ℝ` is symmetric. -/
theorem traceMatrix_real_isSymm (K : Type*) [Field K] [NumberField K] :
    ((Algebra.traceMatrix ℚ (NumberField.integralBasis K)).map (algebraMap ℚ ℝ)).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, mul_comm]

/-- For a number field `K`, the determinant of the real matrix obtained from the trace matrix of
Mathlib's integral basis is `NumberField.discr K`, read in `ℝ`. -/
theorem traceMatrix_real_det (K : Type*) [Field K] [NumberField K] :
    ((Algebra.traceMatrix ℚ (NumberField.integralBasis K)).map (algebraMap ℚ ℝ)).det =
      ((NumberField.discr K : ℤ) : ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, ← Algebra.discr_def,
    ← NumberField.coe_discr]
  simp

/-- For a number field `K` with `r₂` complex places, `discr K = (-1) ^ r₂ * |discr K|` in `ℝ`. -/
theorem discr_eq_neg_one_pow_mul_abs (K : Type*) [Field K] [NumberField K] :
    ((NumberField.discr K : ℤ) : ℝ) =
      (-1 : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces K *
        |((NumberField.discr K : ℤ) : ℝ)| := by
  have h := Int.sign_mul_abs (NumberField.discr K)
  rw [NumberField.sign_discr] at h
  have h' := congrArg (Int.cast : ℤ → ℝ) h
  push_cast at h'
  exact h'.symm

/-- For a number field `K` with `r₂` complex places, the square of the inverse of
`√|discr K|`, times `discr K`, is `(-1) ^ r₂`, in `ℝ`. -/
theorem inv_sqrt_abs_discr_sq_mul_discr (K : Type*) [Field K] [NumberField K] :
    (Real.sqrt |((NumberField.discr K : ℤ) : ℝ)|)⁻¹ ^ 2 * ((NumberField.discr K : ℤ) : ℝ) =
      (-1 : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces K := by
  have hne : ((NumberField.discr K : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast NumberField.discr_ne_zero K
  have hpos : 0 < |((NumberField.discr K : ℤ) : ℝ)| := abs_pos.mpr hne
  rw [inv_pow, Real.sq_sqrt hpos.le]
  nth_rewrite 2 [discr_eq_neg_one_pow_mul_abs K]
  field_simp

end QuarticField

/-- **D4 (the real matrix of the trace form, all signatures).** Let `K` be a number field of degree
four over `ℚ`, and let `G` be the real matrix obtained from the trace matrix
`(Tr_{K/ℚ}(ω i * ω j))` of Mathlib's integral basis `ω = NumberField.integralBasis K` by reading
its rational entries in `ℝ`. On the Lie algebra over `ℝ` of the `G`-skew matrices there is an
`ℝ`-linear endomorphism `H` such that: `H` is bracket-commuting; `H (H X) = (-1) ^ r₂ • X` for all
`X`, where `r₂` is the number of complex places of `K`; and for every bracket-commuting `ℝ`-linear
endomorphism `R` there is exactly one pair `(a, b)` in `ℝ × ℝ` with `R = a • id + b • H`. -/
theorem exists_hodge_traceMatrix_real (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 4) :
    ∃ H : skewAdjointMatricesLieSubalgebra
          ((Algebra.traceMatrix ℚ (NumberField.integralBasis K)).map (algebraMap ℚ ℝ)) →ₗ[ℝ]
        skewAdjointMatricesLieSubalgebra
          ((Algebra.traceMatrix ℚ (NumberField.integralBasis K)).map (algebraMap ℚ ℝ)),
      IsBracketCommuting H ∧
      (∀ X, H (H X) = ((-1 : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces K) • X) ∧
      ∀ R : skewAdjointMatricesLieSubalgebra
            ((Algebra.traceMatrix ℚ (NumberField.integralBasis K)).map (algebraMap ℚ ℝ)) →ₗ[ℝ]
          skewAdjointMatricesLieSubalgebra
            ((Algebra.traceMatrix ℚ (NumberField.integralBasis K)).map (algebraMap ℚ ℝ)),
        IsBracketCommuting R → ∃! ab : ℝ × ℝ, R = ab.1 • LinearMap.id + ab.2 • H := by
  have hne : ((NumberField.discr K : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast NumberField.discr_ne_zero K
  obtain ⟨H, hc, hsq, hu⟩ := exists_hodge_matrix (by norm_num : (2 : ℝ) ≠ 0)
    ((QuarticField.card_integralBasis_index K).trans hK) _
    (QuarticField.traceMatrix_real_isSymm K)
    (by rw [QuarticField.traceMatrix_real_det]; exact hne)
  rw [QuarticField.traceMatrix_real_det] at hsq
  have ht : (Real.sqrt |((NumberField.discr K : ℤ) : ℝ)|)⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_ne_zero'.mpr (abs_pos.mpr hne))
  obtain ⟨hc', hsq', hu'⟩ := FormCentroid.description_smul H _ _ ht hc hsq hu
  rw [QuarticField.inv_sqrt_abs_discr_sq_mul_discr] at hsq'
  exact ⟨_, hc', hsq', hu'⟩

/-- **Control of the clause "not of the form `a • id`" (OPTIONAL).** On the Lie algebra of the
trace-form-skew-adjoint endomorphisms of `S₄` there is a bracket-commuting `ℚ`-linear endomorphism
`R` with `R (R X) = 1 • X` for all `X` (the identity), and there is no rational `t ≠ 0` with
`1 = t ^ 2 * (-283)`. So `exists_nonscalar_sq_iff_S₄` fails at `c = 1` when that clause is
deleted. -/
theorem scalar_sq_control_S₄ :
    (∃ R : skewAdjointLieSubalgebra (Algebra.traceForm ℚ HermiteCompositum.Instance.S₄) →ₗ[ℚ]
          skewAdjointLieSubalgebra (Algebra.traceForm ℚ HermiteCompositum.Instance.S₄),
        IsBracketCommuting R ∧ ∀ X, R (R X) = (1 : ℚ) • X) ∧
      ¬ ∃ t : ℚ, t ≠ 0 ∧ (1 : ℚ) = t ^ 2 * (-283) := by
  refine ⟨⟨LinearMap.id, fun _ _ => rfl, fun X => by simp⟩, ?_⟩
  rintro ⟨t, -, ht⟩
  nlinarith [sq_nonneg t]

namespace QuarticField

/-- The `4 × 4` rational matrix with rows `(0, a, b, 0)`, `(-a, 0, c, 0)`, `(-b, -c, 0, 0)`,
`(p, q, r, d)`. -/
def degMat (a b c p q r d : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, a, b, 0; -a, 0, c, 0; -b, -c, 0, 0; p, q, r, d]

/-- `degMat a b c p q r d` is skew for the diagonal matrix with diagonal `(1, 1, 1, 0)`. -/
theorem degMat_mem (a b c p q r d : ℚ) :
    degMat a b c p q r d ∈ skewAdjointMatricesLieSubalgebra
      (Matrix.diagonal ![1, 1, 1, 0] : Matrix (Fin 4) (Fin 4) ℚ) := by
  refine (mem_etaSkew_iff (![1, 1, 1, 0] : Fin 4 → ℚ) _).mpr fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [degMat]

/-- `degMat a b c p q r d` as an element of the Lie algebra of the matrices skew for the diagonal
matrix with diagonal `(1, 1, 1, 0)`. -/
def degEl (a b c p q r d : ℚ) : skewAdjointMatricesLieSubalgebra
    (Matrix.diagonal ![1, 1, 1, 0] : Matrix (Fin 4) (Fin 4) ℚ) :=
  ⟨degMat a b c p q r d, degMat_mem a b c p q r d⟩

/-- Every matrix `X` skew for the diagonal matrix with diagonal `(1, 1, 1, 0)` is
`degMat (X 0 1) (X 0 2) (X 1 2) (X 3 0) (X 3 1) (X 3 2) (X 3 3)`. -/
theorem coe_eq_degMat (X : skewAdjointMatricesLieSubalgebra
    (Matrix.diagonal ![1, 1, 1, 0] : Matrix (Fin 4) (Fin 4) ℚ)) :
    (X : Matrix (Fin 4) (Fin 4) ℚ) =
      degMat ((X : Matrix (Fin 4) (Fin 4) ℚ) 0 1) ((X : Matrix (Fin 4) (Fin 4) ℚ) 0 2)
        ((X : Matrix (Fin 4) (Fin 4) ℚ) 1 2) ((X : Matrix (Fin 4) (Fin 4) ℚ) 3 0)
        ((X : Matrix (Fin 4) (Fin 4) ℚ) 3 1) ((X : Matrix (Fin 4) (Fin 4) ℚ) 3 2)
        ((X : Matrix (Fin 4) (Fin 4) ℚ) 3 3) := by
  have hX := (mem_etaSkew_iff (![1, 1, 1, 0] : Fin 4 → ℚ) X.1).mp X.2
  have h00 := hX 0 0
  have h11 := hX 1 1
  have h22 := hX 2 2
  have h01 := hX 0 1
  have h02 := hX 0 2
  have h12 := hX 1 2
  have h30 := hX 3 0
  have h31 := hX 3 1
  have h32 := hX 3 2
  simp at h00 h11 h22 h01 h02 h12 h30 h31 h32
  ext i j
  fin_cases i <;> fin_cases j <;> simp [degMat] <;> linarith

/-- An entry of the bracket of two matrices skew for the diagonal matrix with diagonal
`(1, 1, 1, 0)`, written out as sums over the four indices. -/
theorem lie_apply (X Y : skewAdjointMatricesLieSubalgebra
    (Matrix.diagonal ![1, 1, 1, 0] : Matrix (Fin 4) (Fin 4) ℚ)) (i j : Fin 4) :
    ((⁅X, Y⁆ : skewAdjointMatricesLieSubalgebra
          (Matrix.diagonal ![1, 1, 1, 0] : Matrix (Fin 4) (Fin 4) ℚ)) :
        Matrix (Fin 4) (Fin 4) ℚ) i j =
      (X.1 i 0 * Y.1 0 j + X.1 i 1 * Y.1 1 j + X.1 i 2 * Y.1 2 j + X.1 i 3 * Y.1 3 j) -
        (Y.1 i 0 * X.1 0 j + Y.1 i 1 * X.1 1 j + Y.1 i 2 * X.1 2 j + Y.1 i 3 * X.1 3 j) := by
  rw [LieSubalgebra.coe_bracket, Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four]

section Degenerate

/-! In this section `L₀` is the Lie algebra over `ℚ` of the rational `4 × 4` matrices skew for the
diagonal matrix with diagonal `(1, 1, 1, 0)`. -/

local notation "L₀" =>
  skewAdjointMatricesLieSubalgebra (Matrix.diagonal ![1, 1, 1, 0] : Matrix (Fin 4) (Fin 4) ℚ)

/-- If the bracket of `degEl 0 0 0 0 0 0 1` (the matrix unit at `(3, 3)`) with `W` is zero, then
the entries `(3, 0)`, `(3, 1)`, `(3, 2)` of `W` are zero. -/
theorem row_eq_zero_of_lie_eq_zero (W : L₀) (h : ⁅degEl 0 0 0 0 0 0 1, W⁆ = 0) :
    (W : Matrix (Fin 4) (Fin 4) ℚ) 3 0 = 0 ∧ (W : Matrix (Fin 4) (Fin 4) ℚ) 3 1 = 0 ∧
      (W : Matrix (Fin 4) (Fin 4) ℚ) 3 2 = 0 := by
  have h0 := lie_apply (degEl 0 0 0 0 0 0 1) W 3 0
  have h1 := lie_apply (degEl 0 0 0 0 0 0 1) W 3 1
  have h2 := lie_apply (degEl 0 0 0 0 0 0 1) W 3 2
  rw [h] at h0 h1 h2
  simp [degEl, degMat] at h0 h1 h2
  exact ⟨h0.symm, h1.symm, h2.symm⟩

/-- If the entries `(3, 0)`, `(3, 1)`, `(3, 2)` of `W` are zero and the brackets of
`degEl 1 0 0 0 0 0 0` and of `degEl 0 1 0 0 0 0 0` with `W` are zero, then `W` is its `(3, 3)` entry
times `degEl 0 0 0 0 0 0 1`. -/
theorem eq_smul_of_lie_eq_zero (W : L₀) (h30 : (W : Matrix (Fin 4) (Fin 4) ℚ) 3 0 = 0)
    (h31 : (W : Matrix (Fin 4) (Fin 4) ℚ) 3 1 = 0) (h32 : (W : Matrix (Fin 4) (Fin 4) ℚ) 3 2 = 0)
    (hJ1 : ⁅degEl 1 0 0 0 0 0 0, W⁆ = 0) (hJ2 : ⁅degEl 0 1 0 0 0 0 0, W⁆ = 0) :
    W = (W : Matrix (Fin 4) (Fin 4) ℚ) 3 3 • degEl 0 0 0 0 0 0 1 := by
  obtain ⟨a, b, c, p, q, r, d, hW⟩ : ∃ a b c p q r d,
      (W : Matrix (Fin 4) (Fin 4) ℚ) = degMat a b c p q r d :=
    ⟨_, _, _, _, _, _, _, coe_eq_degMat W⟩
  have e1 := lie_apply (degEl 1 0 0 0 0 0 0) W 0 2
  have e2 := lie_apply (degEl 1 0 0 0 0 0 0) W 1 2
  have e3 := lie_apply (degEl 0 1 0 0 0 0 0) W 1 2
  rw [hJ1] at e1 e2
  rw [hJ2] at e3
  rw [hW] at e1 e2 e3 h30 h31 h32
  simp [degEl, degMat] at e1 e2 e3 h30 h31 h32
  apply Subtype.ext
  rw [hW]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [degEl, degMat] <;> linarith

/-- If the entries `(3, 0)`, `(3, 1)`, `(3, 2)` of `U` are zero and the brackets of
`degEl 0 0 0 1 0 0 0` and of `degEl 0 0 0 0 1 0 0` (the matrix units at `(3, 0)` and `(3, 1)`) with
`U` are zero, then `U = 0`. -/
theorem eq_zero_of_lie_eq_zero (U : L₀) (h30 : (U : Matrix (Fin 4) (Fin 4) ℚ) 3 0 = 0)
    (h31 : (U : Matrix (Fin 4) (Fin 4) ℚ) 3 1 = 0) (h32 : (U : Matrix (Fin 4) (Fin 4) ℚ) 3 2 = 0)
    (hP0 : ⁅degEl 0 0 0 1 0 0 0, U⁆ = 0) (hP1 : ⁅degEl 0 0 0 0 1 0 0, U⁆ = 0) : U = 0 := by
  obtain ⟨a, b, c, p, q, r, d, hU⟩ : ∃ a b c p q r d,
      (U : Matrix (Fin 4) (Fin 4) ℚ) = degMat a b c p q r d :=
    ⟨_, _, _, _, _, _, _, coe_eq_degMat U⟩
  have e0 := lie_apply (degEl 0 0 0 1 0 0 0) U 3 0
  have e1 := lie_apply (degEl 0 0 0 1 0 0 0) U 3 1
  have e2 := lie_apply (degEl 0 0 0 1 0 0 0) U 3 2
  have e3 := lie_apply (degEl 0 0 0 0 1 0 0) U 3 2
  rw [hP0] at e0 e1 e2
  rw [hP1] at e3
  rw [hU] at e0 e1 e2 e3 h30 h31 h32
  simp [degEl, degMat] at e0 e1 e2 e3 h30 h31 h32
  apply Subtype.ext
  rw [hU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [degMat] <;> linarith

/-- The bracket of `degEl 0 0 0 0 0 0 1` with `degEl a b c 0 0 0 d` is zero. -/
theorem lie_unit_degEl (a b c d : ℚ) :
    ⁅degEl 0 0 0 0 0 0 1, degEl a b c 0 0 0 d⁆ = 0 := by
  apply Subtype.ext
  ext i j
  rw [lie_apply]
  fin_cases i <;> fin_cases j <;> simp [degEl, degMat]

/-- The bracket of `degEl 0 0 0 p q r 0` with `degEl 0 0 0 0 0 0 1` is `-degEl 0 0 0 p q r 0`. -/
theorem lie_degEl_unit (p q r : ℚ) :
    ⁅degEl 0 0 0 p q r 0, degEl 0 0 0 0 0 0 1⁆ = -degEl 0 0 0 p q r 0 := by
  apply Subtype.ext
  ext i j
  rw [lie_apply]
  fin_cases i <;> fin_cases j <;> simp [degEl, degMat]

/-- The bracket of `degEl 0 0 0 1 0 0 0` (the matrix unit at `(3, 0)`) with `Y` is
`degEl 0 0 0 (-(Y 3 3)) (Y 0 1) (Y 0 2) 0`. -/
theorem lie_row_zero (Y : L₀) :
    ⁅degEl 0 0 0 1 0 0 0, Y⁆ =
      degEl 0 0 0 (-(Y : Matrix (Fin 4) (Fin 4) ℚ) 3 3) ((Y : Matrix (Fin 4) (Fin 4) ℚ) 0 1)
        ((Y : Matrix (Fin 4) (Fin 4) ℚ) 0 2) 0 := by
  obtain ⟨a, b, c, p, q, r, d, hY⟩ : ∃ a b c p q r d,
      (Y : Matrix (Fin 4) (Fin 4) ℚ) = degMat a b c p q r d :=
    ⟨_, _, _, _, _, _, _, coe_eq_degMat Y⟩
  apply Subtype.ext
  ext i j
  rw [lie_apply, hY]
  fin_cases i <;> fin_cases j <;> simp [degEl, degMat]

/-- The bracket of `degEl 0 0 0 0 1 0 0` (the matrix unit at `(3, 1)`) with `Y` is
`degEl 0 0 0 (-(Y 0 1)) (-(Y 3 3)) (Y 1 2) 0`. -/
theorem lie_row_one (Y : L₀) :
    ⁅degEl 0 0 0 0 1 0 0, Y⁆ =
      degEl 0 0 0 (-(Y : Matrix (Fin 4) (Fin 4) ℚ) 0 1) (-(Y : Matrix (Fin 4) (Fin 4) ℚ) 3 3)
        ((Y : Matrix (Fin 4) (Fin 4) ℚ) 1 2) 0 := by
  obtain ⟨a, b, c, p, q, r, d, hY⟩ : ∃ a b c p q r d,
      (Y : Matrix (Fin 4) (Fin 4) ℚ) = degMat a b c p q r d :=
    ⟨_, _, _, _, _, _, _, coe_eq_degMat Y⟩
  apply Subtype.ext
  ext i j
  rw [lie_apply, hY]
  fin_cases i <;> fin_cases j <;> simp [degEl, degMat]

/-- Every `X` is `degEl (X 0 1) (X 0 2) (X 1 2) 0 0 0 (X 3 3)` plus
`degEl 0 0 0 (X 3 0) (X 3 1) (X 3 2) 0`. -/
theorem eq_degEl_add_degEl (X : L₀) :
    X = degEl ((X : Matrix (Fin 4) (Fin 4) ℚ) 0 1) ((X : Matrix (Fin 4) (Fin 4) ℚ) 0 2)
          ((X : Matrix (Fin 4) (Fin 4) ℚ) 1 2) 0 0 0 ((X : Matrix (Fin 4) (Fin 4) ℚ) 3 3) +
        degEl 0 0 0 ((X : Matrix (Fin 4) (Fin 4) ℚ) 3 0) ((X : Matrix (Fin 4) (Fin 4) ℚ) 3 1)
          ((X : Matrix (Fin 4) (Fin 4) ℚ) 3 2) 0 := by
  obtain ⟨a, b, c, p, q, r, d, hX⟩ : ∃ a b c p q r d,
      (X : Matrix (Fin 4) (Fin 4) ℚ) = degMat a b c p q r d :=
    ⟨_, _, _, _, _, _, _, coe_eq_degMat X⟩
  apply Subtype.ext
  rw [hX]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [degEl, degMat]

/-- Let `R` be a linear map with `R ⁅X, Y⁆ = ⁅X, R Y⁆` for all `X`, `Y`, and with
`R (degEl 0 0 0 p q r 0) = δ • degEl 0 0 0 p q r 0` for all `p`, `q`, `r`. If the bracket of
`degEl 0 0 0 0 0 0 1` with `Y` is zero, then `R Y = δ • Y`. -/
theorem apply_eq_smul_of_lie_eq_zero (R : L₀ →ₗ[ℚ] L₀) (hR : ∀ X Y : L₀, R ⁅X, Y⁆ = ⁅X, R Y⁆)
    (δ : ℚ)
    (hP : ∀ p q r : ℚ, R (degEl 0 0 0 p q r 0) = δ • degEl 0 0 0 p q r 0) (Y : L₀)
    (hY : ⁅degEl 0 0 0 0 0 0 1, Y⁆ = 0) : R Y = δ • Y := by
  have hU : ⁅degEl 0 0 0 0 0 0 1, R Y - δ • Y⁆ = 0 := by
    rw [lie_sub, lie_smul, ← hR, hY, map_zero, smul_zero, sub_zero]
  obtain ⟨h30, h31, h32⟩ := row_eq_zero_of_lie_eq_zero _ hU
  have h0 : ⁅degEl 0 0 0 1 0 0 0, R Y - δ • Y⁆ = 0 := by
    rw [lie_sub, lie_smul, ← hR, lie_row_zero, hP, sub_self]
  have h1 : ⁅degEl 0 0 0 0 1 0 0, R Y - δ • Y⁆ = 0 := by
    rw [lie_sub, lie_smul, ← hR, lie_row_one, hP, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_lie_eq_zero _ h30 h31 h32 h0 h1)

end Degenerate

end QuarticField

/-- **Control of D1M, hypothesis `det G ≠ 0` deleted (OPTIONAL).** For the rational diagonal matrix
with diagonal `(1, 1, 1, 0)` (symmetric, determinant `0`), every bracket-commuting `ℚ`-linear
endomorphism `R` of the Lie algebra of the skew matrices is of the form `c • id` with `c` rational.
So no `H` satisfies the conclusion of D1M for this matrix. -/
theorem diag_degenerate_centroid_scalar
    (R : skewAdjointMatricesLieSubalgebra
          (Matrix.diagonal ![1, 1, 1, 0] : Matrix (Fin 4) (Fin 4) ℚ) →ₗ[ℚ]
        skewAdjointMatricesLieSubalgebra
          (Matrix.diagonal ![1, 1, 1, 0] : Matrix (Fin 4) (Fin 4) ℚ))
    (hR : IsBracketCommuting R) : ∃ c : ℚ, R = c • LinearMap.id := by
  have hR' : ∀ X Y, R ⁅X, Y⁆ = ⁅X, R Y⁆ := hR
  have hDD : ⁅QuarticField.degEl 0 0 0 0 0 0 1, R (QuarticField.degEl 0 0 0 0 0 0 1)⁆ = 0 := by
    rw [← hR', lie_self, map_zero]
  obtain ⟨h30, h31, h32⟩ := QuarticField.row_eq_zero_of_lie_eq_zero _ hDD
  have hJ1 : ⁅QuarticField.degEl 1 0 0 0 0 0 0, R (QuarticField.degEl 0 0 0 0 0 0 1)⁆ = 0 := by
    rw [← hR', ← lie_skew, QuarticField.lie_unit_degEl, neg_zero, map_zero]
  have hJ2 : ⁅QuarticField.degEl 0 1 0 0 0 0 0, R (QuarticField.degEl 0 0 0 0 0 0 1)⁆ = 0 := by
    rw [← hR', ← lie_skew, QuarticField.lie_unit_degEl, neg_zero, map_zero]
  obtain ⟨δ, hD⟩ : ∃ δ : ℚ, R (QuarticField.degEl 0 0 0 0 0 0 1) =
      δ • QuarticField.degEl 0 0 0 0 0 0 1 :=
    ⟨_, QuarticField.eq_smul_of_lie_eq_zero _ h30 h31 h32 hJ1 hJ2⟩
  have hP : ∀ p q r : ℚ, R (QuarticField.degEl 0 0 0 p q r 0) =
      δ • QuarticField.degEl 0 0 0 p q r 0 := by
    intro p q r
    have h := hR' (QuarticField.degEl 0 0 0 p q r 0) (QuarticField.degEl 0 0 0 0 0 0 1)
    rw [hD, lie_smul, QuarticField.lie_degEl_unit, map_neg, smul_neg, neg_inj] at h
    exact h
  refine ⟨δ, LinearMap.ext fun X => ?_⟩
  rw [LinearMap.smul_apply, LinearMap.id_apply]
  nth_rewrite 1 [QuarticField.eq_degEl_add_degEl X]
  rw [map_add, hP,
    QuarticField.apply_eq_smul_of_lie_eq_zero R hR' δ hP _ (QuarticField.lie_unit_degEl _ _ _ _),
    ← smul_add, ← QuarticField.eq_degEl_add_degEl X]

end LorentzLie
