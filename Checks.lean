module
public import Mathlib
public import Solution

@[expose] public section
/-!
# Three checks on the compared statements (not compared)

Three theorems proved from the compared statements of `Solution.lean`. They are not part of the
comparison. `degenerate_idempotent_control`: nondegeneracy cannot be dropped from statement 2(c).
`det_traceForm_of_root`: from statements 2(a) and 9(a), the Gram determinant of the trace form
of a number field of degree four containing a root of `x⁴ - x - 1` is `t ^ 2 * (-283)` in every
basis. `isometry_hypotheses_control`: neither hypothesis on `H` can be dropped from statement
4(c).
-/

set_option autoImplicit false

/-! ## Checks (not compared): what the compared statements give together, and hypothesis controls

These are stated on the compared statements themselves (no attribute line, the entry's own
`IsBracketCommuting`). -/

namespace QuaternaryCentroid.Checks

open QuaternaryCentroid

/-- Control for nondegeneracy in statement 2(c): for the degenerate diagonal form `(1, 1, 1, 0)`
over `ℚ` the determinant `0` is a square, and there is no bracket-commuting idempotent other than
`0` and `id`. -/
theorem degenerate_idempotent_control :
    IsSquare ((Matrix.diagonal ![1, 1, 1, 0] : Matrix (Fin 4) (Fin 4) ℚ).det) ∧
    ∀ P : skewAdjointMatricesLieSubalgebra
          (Matrix.diagonal ![1, 1, 1, 0] : Matrix (Fin 4) (Fin 4) ℚ) →ₗ[ℚ]
        skewAdjointMatricesLieSubalgebra
          (Matrix.diagonal ![1, 1, 1, 0] : Matrix (Fin 4) (Fin 4) ℚ),
      IsBracketCommuting P → (∀ X, P (P X) = P X) → P = 0 ∨ P = LinearMap.id := by
  refine ⟨⟨0, by simp [Matrix.det_diagonal, Fin.prod_univ_four]⟩, fun P hP hPP => ?_⟩
  obtain ⟨c, rfl⟩ := controls.2.1 P hP
  have hX : LorentzLie.QuarticField.degEl 1 0 0 0 0 0 0 ≠ 0 := by
    intro h0
    have h1 := congrFun (congrFun (congrArg Subtype.val h0) 0) 1
    simp [LorentzLie.QuarticField.degEl, LorentzLie.QuarticField.degMat] at h1
  have h := hPP (LorentzLie.QuarticField.degEl 1 0 0 0 0 0 0)
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul] at h
  have h3 : (c * c - c) • LorentzLie.QuarticField.degEl 1 0 0 0 0 0 0 = 0 := by
    rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · have h5 : c * (c - 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.mp h5 with h6 | h6
    · left; rw [h6, zero_smul]
    · right; rw [sub_eq_zero.mp h6, one_smul]
  · exact absurd h4 hX

/-- A consequence of statements 9(a) and 2(a): for a number field `K` with a root of
`x⁴ - x - 1`, the determinant of the Gram matrix of the trace form in any basis indexed by a type
with four elements is `t ^ 2 * (-283)` for some rational `t ≠ 0`. With statement 3, after
identifying the rational matrices skew for `diag(1, 1, 1, -1)` with that form's Lie algebra on
`ℚ⁴`, this gives a second route to statement 10(a); the compared proof of 10(a) carries the map
of 10(b) along the equivalence and uses the fact of 9(b). -/
theorem det_traceForm_of_root (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 4) (θ : K) (hθ : θ ^ 4 = θ + 1) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (hι : Fintype.card ι = 4) (b : Module.Basis ι ℚ K) :
    ∃ t : ℚ, t ≠ 0 ∧
      (LinearMap.BilinForm.toMatrix b (Algebra.traceForm ℚ K)).det = t ^ 2 * (-283) := by
  obtain ⟨H, hH, hH2, hu⟩ := (centroid_traceForm_of_root K hK θ hθ).1
  have hs : ¬ ∃ a : ℚ, H = a • LinearMap.id := by
    rintro ⟨a, rfl⟩
    have hid : IsBracketCommuting (LinearMap.id :
        skewAdjointLieSubalgebra (Algebra.traceForm ℚ K) →ₗ[ℚ] _) := fun _ _ => rfl
    obtain ⟨ab, -, huniq⟩ := hu _ hid
    have e1 := huniq (1, 0) (by simp)
    have e2 := huniq (0, a⁻¹) (by
      by_cases ha : a = 0
      · exfalso
        have h1 := huniq (1, 1) (by simp [ha])
        have h2 := huniq (1, 0) (by simp)
        have h3 := congrArg Prod.snd (h1.trans h2.symm)
        exact one_ne_zero h3
      · simp [smul_smul, inv_mul_cancel₀ ha])
    have h3 := congrArg Prod.fst (e1.trans e2.symm)
    exact one_ne_zero h3
  exact ((sq_and_idempotent_iff (by norm_num : (2 : ℚ) ≠ 0) hι b (Algebra.traceForm ℚ K)
    (Algebra.traceForm_isSymm ℚ) (traceForm_nondegenerate ℚ K)).1 (-283)).mp ⟨H, hH, hs, hH2⟩
    |> fun ⟨t, ht, h⟩ => ⟨t⁻¹, inv_ne_zero ht, by
      have h4 : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
      linear_combination (-(t⁻¹ ^ 2)) * h -
        ((LinearMap.BilinForm.toMatrix b (Algebra.traceForm ℚ K)).det * (1 + t * t⁻¹)) * h4⟩

/-- Controls for the two hypotheses on `H` in statement 4(c). For a form as in statement 1 there
are a `B`-preserving map `g` and the conjugation `φ` by `g` such that the conclusion
`φ ∘ R ∘ φ⁻¹ = det g • R` fails (i) for `R = id`, which is bracket-commuting and of the form
`a • id`, and (ii) for some bracket-commuting `R` that is not of the form `a • id` (namely
`id + H`, whose square is not a scalar). -/
theorem isometry_hypotheses_control {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype ι] [DecidableEq ι] (h2 : (2 : F) ≠ 0) (hι : Fintype.card ι = 4)
    (b : Module.Basis ι F V) (B : LinearMap.BilinForm F V) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) :
    ∃ (g : V →ₗ[F] V) (φ : skewAdjointLieSubalgebra B ≃ₗ⁅F⁆ skewAdjointLieSubalgebra B),
      (∀ x y : V, B (g x) (g y) = B x y) ∧
      (∀ (X : skewAdjointLieSubalgebra B) (x : V),
        (φ X : Module.End F V) (g x) = g ((X : Module.End F V) x)) ∧
      (¬ ∀ X : skewAdjointLieSubalgebra B, φ (φ.symm X) = LinearMap.det g • X) ∧
      ∃ R : skewAdjointLieSubalgebra B →ₗ[F] skewAdjointLieSubalgebra B,
        IsBracketCommuting R ∧ (¬ ∃ a : F, R = a • LinearMap.id) ∧
        ¬ ∀ X, φ (R (φ.symm X)) = LinearMap.det g • R X := by
  obtain ⟨hall, g, hg, hdet⟩ := isometry_conj_eq_det_smul h2 hι b B hB hnd
  obtain ⟨-, ⟨φ, hφ⟩, hconj⟩ := hall g hg
  obtain ⟨H, hc, hsq, hu, -⟩ := centroid_of_dim_four h2 hι b B hB hnd
  have hHs : ¬ ∃ a : F, H = a • LinearMap.id := by
    rintro ⟨a, ha⟩
    obtain ⟨ab, -, huniq⟩ := hu H hc
    have e1 := huniq (0, 1) (by simp)
    have e2 := huniq (a, 0) (by simpa using ha)
    exact one_ne_zero (congrArg Prod.snd (e1.trans e2.symm))
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : skewAdjointLieSubalgebra B, X₀ ≠ 0 := by
    by_contra hno
    have hno' : ∀ X : skewAdjointLieSubalgebra B, X = 0 := fun X =>
      by_contra fun h => hno ⟨X, h⟩
    exact hHs ⟨0, LinearMap.ext fun X => by rw [hno' X]; simp⟩
  have h2X : (2 : F) • X₀ ≠ 0 := smul_ne_zero h2 hX₀
  have hH := hconj φ hφ H hc hHs ⟨_, hsq⟩
  refine ⟨g, φ, hg, hφ, ?_, LinearMap.id + H, ?_, ?_, ?_⟩
  · intro hall'
    have h1 := hall' X₀
    rw [LieEquiv.apply_symm_apply, hdet, neg_one_smul] at h1
    exact h2X (by rw [two_smul]; exact eq_neg_iff_add_eq_zero.mp h1)
  · intro X Y
    simp only [LinearMap.add_apply, LinearMap.id_apply, lie_add]
    rw [hc X Y]
  · rintro ⟨a, ha⟩
    refine hHs ⟨a - 1, ?_⟩
    have h5 : H = a • LinearMap.id - LinearMap.id := by rw [← ha, add_sub_cancel_left]
    rw [h5]
    module
  · intro hall'
    have h1 := hall' X₀
    rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.id_apply, LinearMap.id_apply,
      map_add, LieEquiv.apply_symm_apply, hH, hdet, smul_add] at h1
    have h3 : X₀ = (-1 : F) • X₀ := add_right_cancel h1
    rw [neg_one_smul] at h3
    exact h2X (by rw [two_smul]; exact eq_neg_iff_add_eq_zero.mp h3)

end QuaternaryCentroid.Checks
