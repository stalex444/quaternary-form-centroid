module
public import Mathlib
public import QuaternaryCentroid.Bridge

@[expose] public section
/-!
# Bracket-commuting maps of the orthogonal Lie algebra of a quaternary form: proofs

Each of the eleven statements of `Challenge.lean` is proved here, with the identical statement and
the identical definition `IsBracketCommuting`, which is repeated verbatim. Each proof is one
`exact` of a theorem of the libraries of this repository:

* Statement 1: `QuaternaryCentroid.Bridge.lead`, from `LorentzLie.exists_hodge_of_basis` and
  `LorentzLie.hodge_of_basis_eq_or_eq_neg` (`LorentzLie/FormCentroid.lean`). For a diagonal form
  with nonzero entries `η` the operator is explicit, `X ↦ star0 (diagonal η * X) * diagonal η`
  (`LorentzLie.hodge`, `LorentzLie/Defs.lean`); that it commutes with the bracket, has square
  `∏ i, η i`, and that every bracket-commuting map is a combination of it and the identity are
  computations with the six matrices `η j • E i j - η i • E j i` (`LorentzLie/Centroid.lean`). For
  a symmetric Gram matrix `G` of nonzero determinant, the `G`-skew matrices are Lie-equivalent to
  the skew matrices of a diagonal form whose determinant is `t ^ 2 * det G`
  (`LorentzLie.FormCentroid.exists_lieEquiv_etaSkew`); the description is carried along that
  equivalence (`LorentzLie.centroid_transport_field`), the operator is divided by `t`, and the
  result is carried to the endomorphisms by the matrix of an endomorphism in the basis.
* Statement 2: `QuaternaryCentroid.Bridge.squares`: arithmetic with `a • id + b • H` and
  `H ∘ H = det B`, from statement 1's description.
* Statement 3: `LorentzLie.det_toMatrix_eq_sq_mul_of_lieEquiv`: the Lie algebra equivalence
  carries the operator of `B'` to a bracket-commuting map of `so(B)`, not of the form `a • id`,
  whose square is `det B'`; statement 2(a) for `B` then gives `det B' = t ^ 2 * det B`.
* Statement 4: `QuaternaryCentroid.Bridge.isometry_det`, `exists_conj_lieEquiv`,
  `isometry_conj_of_basis`, `exists_isometry_det_neg_one`. Conjugation sends `H` to `H` or `-H`
  (statement 1(d)); in an orthogonal basis one matrix entry of the conjugated operator is the
  determinant of the matrix of `g`, which identifies the sign. The map of determinant `-1` is a
  reflection in a vector of an orthogonal basis.
* Statement 5: `LorentzLie.centroid_scalar_of_basis`; statement 6: `LorentzLie.centroid_scalar_so'`.
  Both rest on `LorentzLie.centroid_scalar_of_two_ne_zero` (`LorentzLie/Centroid.lean`), for a
  diagonal form with nonzero entries on an index type with a number of elements other than four:
  the image of a generator `η j • E i j - η i • E j i` commutes with everything that commutes with
  the generator, which forces it to be a multiple of the generator; and the elements on which two
  bracket-commuting maps agree are stable under every `⁅X, ·⁆`.
* Statement 7: `QuaternaryCentroid.Bridge.real_diagonal`, from the explicit operator; for the
  product `1` the idempotent is `½ (id + H)`.
* Statement 8: `LorentzLie.exists_hodge_traceForm`, `LorentzLie.exists_sq_neg_one_iff_traceForm`,
  `LorentzLie.exists_hodge_traceMatrix_real` (`LorentzLie/QuarticField.lean`): statement 1 for the
  trace form in Mathlib's integral basis, whose Gram determinant is the discriminant, with
  Mathlib's `NumberField.sign_discr` for the real clause.
* Statements 9–11: `QuaternaryCentroid.Bridge.root_instance`, `not_lieEquiv_diag`, `exists_root`,
  `scalar_control`, with `LorentzLie.diag_exists_sq_neg_one_rat` and
  `LorentzLie.diag_degenerate_centroid_scalar`. The discriminant `-283` of a number field of
  degree four containing a root of `x⁴ - x - 1` is taken from the library `HermiteCompositum`
  (`QuaternaryCentroid.Bridge.discr_of_root`).

The libraries state their theorems with `LorentzLie.IsBracketCommuting`, which has the same body as
the definition below, and declare `attribute [local instance] LieRing.ofAssociativeRing`. This file
declares neither an attribute nor an `open`, as `Challenge.lean`; each `exact` is accepted because
the two statements are definitionally equal.
-/

set_option autoImplicit false

namespace QuaternaryCentroid

/-- A linear endomorphism `R` of a Lie algebra `L` over a commutative ring `K` is
*bracket-commuting* when `R ⁅X, Y⁆ = ⁅X, R Y⁆` for all `X`, `Y` in `L`. By antisymmetry of the
bracket this is the same as `R ⁅X, Y⁆ = ⁅R X, Y⁆` for all `X`, `Y`. The set of bracket-commuting
maps is what is usually called the centroid of `L`. -/
def IsBracketCommuting {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    (R : L →ₗ[K] L) : Prop :=
  ∀ X Y : L, R ⁅X, Y⁆ = ⁅X, R Y⁆

/-! ### The general theorem -/

/-- **1. The bracket-commuting maps in dimension four.** Let `F` be a field with `2 ≠ 0`, `V` a
vector space over `F` with a basis `b` indexed by a finite type `ι` with exactly four elements, and
`B` a symmetric nondegenerate bilinear form on `V`. Write `d` for the determinant of the Gram matrix
of `B` in the basis `b`. Then, on the Lie algebra of the `B`-skew-adjoint endomorphisms of `V`,
there is an `F`-linear endomorphism `H` such that:
(a) `H` is bracket-commuting;
(b) `H (H X) = d • X` for all `X`;
(c) for every bracket-commuting `F`-linear endomorphism `R` there is exactly one pair `(a, c)` in
`F × F` with `R = a • id + c • H`;
(d) every bracket-commuting `F`-linear endomorphism `H'` that is not of the form `a • id` and
satisfies `H' (H' X) = d • X` for all `X` is `H` or `-H`.
So the bracket-commuting maps are a copy of the quadratic algebra `F[X]/(X² - d)`. The square
class: for `t ≠ 0`, the operator `t • H` has (a) and (c), and (b) with `t ^ 2 * d` in place of `d`;
what is determined is the class of `d` modulo nonzero squares (statements 2 and 3). -/
theorem centroid_of_dim_four {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
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
  exact Bridge.lead h2 hι b B hB hnd

/-- **2. Squares and idempotents among the bracket-commuting maps.** Let `F` be a field with
`2 ≠ 0`, `V` a vector space over `F` with a basis `b` indexed by a finite type `ι` with exactly
four elements, and `B` a symmetric nondegenerate bilinear form on `V`. Write `d` for the
determinant of the Gram matrix of `B` in the basis `b`. On the Lie algebra of the `B`-skew-adjoint
endomorphisms of `V`:
(a) for every `c` in `F`, there is a bracket-commuting `F`-linear endomorphism `R` that is not of
the form `a • id` and satisfies `R (R X) = c • X` for all `X`, if and only if `c = t ^ 2 * d` for
some `t ≠ 0` in `F`;
(b) there is a bracket-commuting `R` with `R (R X) = -X` for all `X`, if and only if `-d` is a
square in `F` or `-1` is a square in `F` (the second alternative is the case `R = a • id` with
`a ^ 2 = -1`);
(c) there is a bracket-commuting `P` with `P (P X) = P X` for all `X` that is neither `0` nor the
identity, if and only if `d` is a square in `F`;
(d) if `P` and `Q` are two bracket-commuting endomorphisms as in (c), then `Q = P` or
`Q = id - P`.
These are the corresponding facts about the quadratic algebra `F[X]/(X² - d)`. Each of the
conditions on `d` in (a), (b), (c) depends only on the class of `d` modulo nonzero squares. -/
theorem sq_and_idempotent_iff {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
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
  exact Bridge.squares h2 hι b B hB hnd

/-- **3. The square class of the determinant is determined by the Lie algebra.** Let `F` be a
field with `2 ≠ 0`. Let `V` and `V'` be vector spaces over `F` with bases `b` and `b'` indexed by
finite types `ι` and `ι'` with exactly four elements each, and let `B` on `V` and `B'` on `V'` be
symmetric nondegenerate bilinear forms. If there is a Lie algebra equivalence from the Lie algebra
of the `B`-skew-adjoint endomorphisms of `V` to that of the `B'`-skew-adjoint endomorphisms of `V'`,
then there is `t ≠ 0` in `F` such that the determinant of the Gram matrix of `B'` in `b'` is `t ^ 2`
times the determinant of the Gram matrix of `B` in `b`. -/
theorem det_eq_sq_mul_of_lieEquiv {F V ι : Type*} [Field F] [AddCommGroup V]
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
  exact LorentzLie.det_toMatrix_eq_sq_mul_of_lieEquiv h2 hι hι' b b' B hB hnd B' hB' hnd' e

/-- **4. A linear map preserving the form acts on `H` by its determinant.** Let `F` be a field
with `2 ≠ 0`, `V` a vector space over `F` with a basis `b` indexed by a finite type `ι` with
exactly four elements, `B` a symmetric nondegenerate bilinear form on `V`, and `L` the Lie algebra
of the `B`-skew-adjoint endomorphisms of `V`.
For every `F`-linear endomorphism `g` of `V` with `B (g x) (g y) = B x y` for all `x`, `y`:
(a) `det g` is `1` or `-1`;
(b) there is a Lie algebra equivalence `φ` from `L` to `L` with `(φ X) (g x) = g (X x)` for all `X`
in `L` and `x` in `V` (conjugation by `g`);
(c) for every such `φ` and every bracket-commuting `F`-linear endomorphism `H` of `L` that is not
of the form `a • id` and satisfies `H (H X) = c • X` for all `X`, for some `c` in `F`:
`φ (H (φ⁻¹ X)) = det g • H X` for all `X`, that is, the map `φ ∘ H ∘ φ⁻¹` is `det g • H`.
(d) There is an `F`-linear endomorphism `g` of `V` with `B (g x) (g y) = B x y` for all `x`, `y`
and `det g = -1`.
By statement 1 every bracket-commuting map is `a • id + c • H`. So conjugation by `g` fixes every
bracket-commuting map when `det g = 1`, and is `a • id + c • H ↦ a • id - c • H` when
`det g = -1`; by (d) both cases occur. -/
theorem isometry_conj_eq_det_smul {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype ι] (h2 : (2 : F) ≠ 0) (hι : Fintype.card ι = 4)
    (b : Module.Basis ι F V) (B : LinearMap.BilinForm F V) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) :
    (∀ g : V →ₗ[F] V, (∀ x y : V, B (g x) (g y) = B x y) →
      (LinearMap.det g = 1 ∨ LinearMap.det g = -1) ∧
      (∃ φ : skewAdjointLieSubalgebra B ≃ₗ⁅F⁆ skewAdjointLieSubalgebra B,
        ∀ (X : skewAdjointLieSubalgebra B) (x : V),
          (φ X : Module.End F V) (g x) = g ((X : Module.End F V) x)) ∧
      ∀ φ : skewAdjointLieSubalgebra B ≃ₗ⁅F⁆ skewAdjointLieSubalgebra B,
        (∀ (X : skewAdjointLieSubalgebra B) (x : V),
          (φ X : Module.End F V) (g x) = g ((X : Module.End F V) x)) →
        ∀ H : skewAdjointLieSubalgebra B →ₗ[F] skewAdjointLieSubalgebra B,
          IsBracketCommuting H → (¬ ∃ a : F, H = a • LinearMap.id) →
          (∃ c : F, ∀ X, H (H X) = c • X) →
          ∀ X, φ (H (φ.symm X)) = LinearMap.det g • H X) ∧
    ∃ g : V →ₗ[F] V, (∀ x y : V, B (g x) (g y) = B x y) ∧ LinearMap.det g = -1 := by
  exact ⟨fun g hg => ⟨Bridge.isometry_det b B hnd g hg, Bridge.exists_conj_lieEquiv b B hnd g hg,
    fun φ hφ H hH hHs ⟨c, hc⟩ X =>
      Bridge.isometry_conj_of_basis h2 hι b B hB hnd g hg φ hφ H hH hHs c hc X⟩,
    Bridge.exists_isometry_det_neg_one h2 hι b B hB hnd⟩

/-! ### Other dimensions -/

/-- **5. In every other finite dimension the bracket-commuting maps are scalars.** Let `F` be a
field with `2 ≠ 0`, `V` a vector space over `F` with a basis `b` indexed by a finite type `ι` whose
number of elements is not four, and `B` a symmetric nondegenerate bilinear form on `V`. Then every
bracket-commuting `F`-linear endomorphism `R` of the Lie algebra of the `B`-skew-adjoint
endomorphisms of `V` is of the form `c • id` with `c` in `F`. -/
theorem centroid_scalar_of_dim_ne_four {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype ι] (h2 : (2 : F) ≠ 0) (hι : Fintype.card ι ≠ 4)
    (b : Module.Basis ι F V) (B : LinearMap.BilinForm F V) (hB : B.IsSymm)
    (hnd : B.Nondegenerate)
    (R : skewAdjointLieSubalgebra B →ₗ[F] skewAdjointLieSubalgebra B)
    (hR : IsBracketCommuting R) : ∃ c : F, R = c • LinearMap.id := by
  exact LorentzLie.centroid_scalar_of_basis h2 hι b B hB hnd R hR

/-- **6. Example: Mathlib's `so' p q ℝ` outside dimension four.** Let `p` and `q` be finite types
with `card p + card q ≠ 4`, and let `R` be a bracket-commuting real-linear endomorphism of
Mathlib's `LieAlgebra.Orthogonal.so' p q ℝ` (the real matrices indexed by `p ⊕ q` that are
skew-adjoint for the diagonal form with entries `1` on `p` and `-1` on `q`). Then `R = c • id` for
some real `c`. This is the fact of statement 5 for these matrix Lie algebras. -/
theorem centroid_scalar_so' {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (h : Fintype.card p + Fintype.card q ≠ 4)
    (R : LieAlgebra.Orthogonal.so' p q ℝ →ₗ[ℝ] LieAlgebra.Orthogonal.so' p q ℝ)
    (hR : IsBracketCommuting R) : ∃ c : ℝ, R = c • LinearMap.id := by
  exact LorentzLie.centroid_scalar_so' h R hR

/-! ### Corollaries and examples -/

/-- **7. Corollary over `ℝ`: diagonal forms with entries `±1` in dimension four.** Let
`η : Fin 4 → ℝ` have every entry equal to `1` or `-1`, and let `L` be the Lie algebra of the real
`4 × 4` matrices that are skew-adjoint for the diagonal matrix with diagonal `η`. The determinant
of the form is the product of the entries of `η`, which is `1` or `-1`.
(a) If the product is `-1` (three entries of one sign and one of the other: signature `(3, 1)` or
`(1, 3)`), there is a bracket-commuting real-linear endomorphism `J` of `L` with `J (J X) = -X`
for all `X`, such that every bracket-commuting `R` is `a • id + c • J` for exactly one pair
`(a, c)` of real numbers. The bracket-commuting maps are a copy of `ℂ`.
(b) If the product is `1` (signature `(4, 0)`, `(0, 4)` or `(2, 2)`), there is a bracket-commuting
real-linear endomorphism `P` of `L` with `P (P X) = P X` for all `X`, neither `0` nor the identity,
such that every bracket-commuting `R` is `a • P + c • (id - P)` for exactly one pair `(a, c)` of
real numbers. The bracket-commuting maps are a copy of `ℝ × ℝ`.
This is statements 1 and 2 over `ℝ`, where the class of the determinant modulo squares is its
sign. -/
theorem centroid_real_diagonal (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1) :
    (∏ i, η i = -1 →
      ∃ J : skewAdjointMatricesLieSubalgebra (Matrix.diagonal η) →ₗ[ℝ]
          skewAdjointMatricesLieSubalgebra (Matrix.diagonal η),
        IsBracketCommuting J ∧ (∀ X, J (J X) = -X) ∧
        ∀ R : skewAdjointMatricesLieSubalgebra (Matrix.diagonal η) →ₗ[ℝ]
            skewAdjointMatricesLieSubalgebra (Matrix.diagonal η), IsBracketCommuting R →
          ∃! ab : ℝ × ℝ, R = ab.1 • LinearMap.id + ab.2 • J) ∧
    (∏ i, η i = 1 →
      ∃ P : skewAdjointMatricesLieSubalgebra (Matrix.diagonal η) →ₗ[ℝ]
          skewAdjointMatricesLieSubalgebra (Matrix.diagonal η),
        IsBracketCommuting P ∧ P ≠ 0 ∧ P ≠ LinearMap.id ∧ (∀ X, P (P X) = P X) ∧
        ∀ R : skewAdjointMatricesLieSubalgebra (Matrix.diagonal η) →ₗ[ℝ]
            skewAdjointMatricesLieSubalgebra (Matrix.diagonal η), IsBracketCommuting R →
          ∃! ab : ℝ × ℝ, R = ab.1 • P + ab.2 • (LinearMap.id - P)) := by
  exact Bridge.real_diagonal η hη

/-- **8. Corollary: the trace form of a number field of degree four.** Let `K` be a number field
of degree four over `ℚ`, with discriminant `d_K` (Mathlib's `NumberField.discr K`, an integer, read
in `ℚ`), and let `L` be the Lie algebra over `ℚ` of the `ℚ`-linear endomorphisms of `K` that are
skew-adjoint for the trace form `(x, y) ↦ Tr_{K/ℚ}(x * y)`.
(a) There is a bracket-commuting `ℚ`-linear endomorphism `H` of `L` with `H (H X) = d_K • X` for
all `X`, such that every bracket-commuting `R` is `a • id + c • H` for exactly one pair `(a, c)` of
rational numbers. (As in statement 1, what is determined is the class of `d_K` modulo nonzero
rational squares.)
(b) There is a bracket-commuting `ℚ`-linear endomorphism `R` of `L` with `R (R X) = -X` for all
`X`, if and only if `-d_K` is the square of a rational number.
(c) Over `ℝ`: let `G` be the real matrix obtained from the trace matrix `(Tr_{K/ℚ}(ω i * ω j))` of
Mathlib's integral basis `ω = NumberField.integralBasis K` by reading its rational entries in `ℝ`.
On the Lie algebra over `ℝ` of the `G`-skew matrices there is a bracket-commuting `ℝ`-linear
endomorphism `H` with `H (H X) = (-1) ^ r₂ • X` for all `X`, where `r₂` is the number of complex
places of `K`, such that every bracket-commuting `R` is `a • id + c • H` for exactly one pair
`(a, c)` of real numbers. (Over `ℝ` the class modulo nonzero squares is the sign: `t • H` has
square `t ^ 2 * (-1) ^ r₂`, and what is determined is the sign `(-1) ^ r₂`, the sign of `d_K`.) -/
theorem centroid_traceForm (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 4) :
    (∃ H : skewAdjointLieSubalgebra (Algebra.traceForm ℚ K) →ₗ[ℚ]
        skewAdjointLieSubalgebra (Algebra.traceForm ℚ K),
      IsBracketCommuting H ∧ (∀ X, H (H X) = (NumberField.discr K : ℚ) • X) ∧
      ∀ R : skewAdjointLieSubalgebra (Algebra.traceForm ℚ K) →ₗ[ℚ]
          skewAdjointLieSubalgebra (Algebra.traceForm ℚ K), IsBracketCommuting R →
        ∃! ab : ℚ × ℚ, R = ab.1 • LinearMap.id + ab.2 • H) ∧
    ((∃ R : skewAdjointLieSubalgebra (Algebra.traceForm ℚ K) →ₗ[ℚ]
          skewAdjointLieSubalgebra (Algebra.traceForm ℚ K),
        IsBracketCommuting R ∧ ∀ X, R (R X) = -X) ↔
      IsSquare (-(NumberField.discr K : ℚ))) ∧
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
  exact ⟨LorentzLie.exists_hodge_traceForm K hK, LorentzLie.exists_sq_neg_one_iff_traceForm K hK,
    LorentzLie.exists_hodge_traceMatrix_real K hK⟩

/-- **9. Example: the polynomial `x⁴ - x - 1`.** Let `K` be a number field of degree four over
`ℚ` and `θ` an element of `K` with `θ ^ 4 = θ + 1` (statement 11(a): such `K` and `θ` exist). Let
`L` be the Lie algebra over `ℚ` of the `ℚ`-linear endomorphisms of `K` that are skew-adjoint for
the trace form of `K` over `ℚ`.
(a) There is a bracket-commuting `ℚ`-linear endomorphism `H` of `L` with `H (H X) = (-283) • X`
for all `X`, such that every bracket-commuting `R` is `a • id + c • H` for exactly one pair
`(a, c)` of rational numbers. (As in statement 1, what is determined is the class of `-283`
modulo nonzero rational squares.)
(b) No bracket-commuting `ℚ`-linear endomorphism `R` of `L` satisfies `R (R X) = -X` for all `X`
(`283` is not the square of a rational number).
(c) Over `ℝ`, on the Lie algebra of the real matrices that are skew for the trace matrix of
Mathlib's integral basis of `K` (entries read in `ℝ`), there is a bracket-commuting `ℝ`-linear
endomorphism `R` with `R (R X) = -X` for all `X`.
This is statement 8 at one field: the two hypotheses give `K = ℚ(θ)` (the polynomial
`x⁴ - x - 1` is irreducible over `ℚ`), and the discriminant of `K` is `-283`. These two facts are
used in the proof; they are not compared statements of this entry. The hypothesis on the degree
cannot be dropped: a number field of larger degree that contains such a `θ` has only the
bracket-commuting maps `c • id` (statement 5). -/
theorem centroid_traceForm_of_root (K : Type*) [Field K] [NumberField K]
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
  exact Bridge.root_instance K hK θ hθ

/-- **10. Example: two rational forms whose Lie algebras are not isomorphic over `ℚ`.** Let `K` be
a number field of degree four over `ℚ` and `θ` an element of `K` with `θ ^ 4 = θ + 1`.
(a) There is no Lie algebra equivalence over `ℚ` from the Lie algebra of the `ℚ`-linear
endomorphisms of `K` that are skew-adjoint for the trace form of `K` to the Lie algebra of the
rational `4 × 4` matrices that are skew for the diagonal matrix with diagonal `(1, 1, 1, -1)`.
(b) On the second Lie algebra there is a bracket-commuting `ℚ`-linear endomorphism `R` with
`R (R X) = -X` for all `X`.
Reason: a Lie algebra equivalence would carry the map of (b) to a bracket-commuting map of square
`-1` on the first Lie algebra, which statement 9(b) excludes. In the terms of statements 2(b) and
3: the determinants of the two forms are `-283` (up to a rational square) and `-1`, and `283` is
not a rational square. Over `ℝ` the Lie algebras of the two forms both have a bracket-commuting
map of square `-1` (statements 9(c) and 7(a)). -/
theorem not_lieEquiv_diagonal_of_root (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 4) (θ : K) (hθ : θ ^ 4 = θ + 1) :
    IsEmpty (skewAdjointLieSubalgebra (Algebra.traceForm ℚ K) ≃ₗ⁅ℚ⁆
        skewAdjointMatricesLieSubalgebra
          (Matrix.diagonal ![1, 1, 1, -1] : Matrix (Fin 4) (Fin 4) ℚ)) ∧
    ∃ R : skewAdjointMatricesLieSubalgebra
          (Matrix.diagonal ![1, 1, 1, -1] : Matrix (Fin 4) (Fin 4) ℚ) →ₗ[ℚ]
        skewAdjointMatricesLieSubalgebra
          (Matrix.diagonal ![1, 1, 1, -1] : Matrix (Fin 4) (Fin 4) ℚ),
      IsBracketCommuting R ∧ ∀ X, R (R X) = -X := by
  exact ⟨Bridge.not_lieEquiv_diag K hK θ hθ, LorentzLie.diag_exists_sq_neg_one_rat⟩

/-! ### Controls -/

/-- **11. Controls.**
(a) The hypotheses of statements 9 and 10 can be met: there are a number field `K` of degree four
over `ℚ` and an element `θ` of `K` with `θ ^ 4 = θ + 1`.
(b) Nondegeneracy in statement 1: for the rational diagonal matrix with diagonal `(1, 1, 1, 0)`
(symmetric, determinant `0`), every bracket-commuting `ℚ`-linear endomorphism `R` of the Lie
algebra of the skew matrices is of the form `c • id` with `c` rational. So no `H` as in statement 1
exists for this matrix.
(c) The clause "not of the form `a • id`" in statement 2(a): on the Lie algebra of the rational
matrices skew for the diagonal matrix with diagonal `(1, 1, 1, -1)` (determinant `-1`) there is a
bracket-commuting `ℚ`-linear endomorphism `R` with `R (R X) = 1 • X` for all `X` (the identity),
and there is no rational `t ≠ 0` with `1 = t ^ 2 * (-1)`. -/
theorem controls :
    (∃ (K : Type) (_ : Field K) (_ : NumberField K) (θ : K),
      Module.finrank ℚ K = 4 ∧ θ ^ 4 = θ + 1) ∧
    (∀ R : skewAdjointMatricesLieSubalgebra
          (Matrix.diagonal ![1, 1, 1, 0] : Matrix (Fin 4) (Fin 4) ℚ) →ₗ[ℚ]
        skewAdjointMatricesLieSubalgebra
          (Matrix.diagonal ![1, 1, 1, 0] : Matrix (Fin 4) (Fin 4) ℚ),
      IsBracketCommuting R → ∃ c : ℚ, R = c • LinearMap.id) ∧
    (∃ R : skewAdjointMatricesLieSubalgebra
          (Matrix.diagonal ![1, 1, 1, -1] : Matrix (Fin 4) (Fin 4) ℚ) →ₗ[ℚ]
        skewAdjointMatricesLieSubalgebra
          (Matrix.diagonal ![1, 1, 1, -1] : Matrix (Fin 4) (Fin 4) ℚ),
      IsBracketCommuting R ∧ ∀ X, R (R X) = (1 : ℚ) • X) ∧
    ¬ ∃ t : ℚ, t ≠ 0 ∧ (1 : ℚ) = t ^ 2 * (-1) := by
  exact ⟨Bridge.exists_root, fun R hR => LorentzLie.diag_degenerate_centroid_scalar R hR,
    Bridge.scalar_control⟩

end QuaternaryCentroid
