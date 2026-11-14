module
public import Mathlib

@[expose] public section
/-!
# Bracket-commuting maps (the centroid) of the orthogonal Lie algebra of a quaternary form: the quadratic algebra F[X]/(X^2 - det B) and the square class of the determinant

Let `F` be a field with `2 ≠ 0`, `B` a nondegenerate symmetric bilinear form on a four-dimensional
`F`-vector space, and `so(B)` the Lie algebra of the `B`-skew-adjoint endomorphisms. A linear map
`R : so(B) → so(B)` is *bracket-commuting* when `R ⁅X, Y⁆ = ⁅X, R Y⁆` for all `X`, `Y`. The
statements say that the bracket-commuting maps of `so(B)`, i.e. its centroid, are the maps
`a • id + c • H` for one operator `H` with `H ∘ H = det B`, a copy of the quadratic algebra
`F[X]/(X² - det B)`; that the class of `det B` modulo nonzero squares is determined by the Lie
algebra; that a linear map preserving `B` acts on `H` by its determinant; that in every other
finite dimension the bracket-commuting maps are the maps `c • id`; and what this gives over `ℝ`
and for the trace form of a number field of degree four, with the field of `x⁴ - x - 1`
(discriminant `-283`) as the instance: over `ℚ`, the Lie algebra of its trace form is not
isomorphic to the Lie algebra of the diagonal form `(1, 1, 1, -1)`.
This entry compares exactly these eleven statements. It is a formalization; nothing in it is
claimed as original mathematics.

The square class. Wherever a statement below says `H (H X) = d • X`, the same statement holds for
`t • H` with `t ^ 2 * d` in place of `d`, for every `t ≠ 0`, and `det B` itself is the determinant
of the Gram matrix in a chosen basis, which changes by a nonzero square with the basis. What the
Lie algebra determines is the class of `d` modulo nonzero squares (statements 2 and 3).

The general theorem (statements 1–4):

1. `centroid_of_dim_four` — there is a bracket-commuting `H` with `H (H X) = det B • X` such that
   every bracket-commuting map is `a • id + c • H` for exactly one pair `(a, c)`; and a
   bracket-commuting map that is not of the form `a • id` and has the same square is `H` or `-H`.
2. `sq_and_idempotent_iff` — (a) a bracket-commuting map, not of the form `a • id`, with
   `R (R X) = c • X` exists if and only if `c = t ^ 2 * det B` for some `t ≠ 0`; (b) a
   bracket-commuting map, of the form `a • id` or not, with `R (R X) = -X` exists if and only if
   `-det B` or `-1` is a square; (c) a bracket-commuting idempotent other than `0` and `id` exists
   if and only if `det B` is a square; (d) when they exist there are exactly two, `P` and `id - P`.
3. `det_eq_sq_mul_of_lieEquiv` — if `so(B)` and `so(B')` are isomorphic Lie algebras, then
   `det B' = t ^ 2 * det B` for some `t ≠ 0`.
4. `isometry_conj_eq_det_smul` — if `g` is a linear map preserving `B`, then `det g = ±1`,
   conjugation by `g` is a Lie algebra equivalence `φ` of `so(B)`, and `φ ∘ H ∘ φ⁻¹ = det g • H`
   for every bracket-commuting `H`, not of the form `a • id`, whose square is a scalar; a map
   preserving `B` with determinant `-1` exists.

Other dimensions (statements 5–6):

5. `centroid_scalar_of_dim_ne_four` — for a nondegenerate symmetric form in any finite dimension
   other than four, every bracket-commuting map of `so(B)` is `c • id`.
6. `centroid_scalar_so'` — an example of the same fact on Mathlib's `so' p q ℝ`: when
   `card p + card q ≠ 4`, every bracket-commuting map is `c • id`.

Corollaries and examples (statements 7–10):

7. `centroid_real_diagonal` — over `ℝ`, for a diagonal form with entries `±1` in dimension four:
   if the product of the entries is `-1` (signature `(3, 1)` or `(1, 3)`), the bracket-commuting
   maps are `a • id + c • J` with `J (J X) = -X`, a copy of `ℂ`; if the product is `1` (signature
   `(4, 0)`, `(0, 4)` or `(2, 2)`), they are `a • P + c • (id - P)` for a bracket-commuting
   idempotent `P` other than `0` and `id`, a copy of `ℝ × ℝ`.
8. `centroid_traceForm` — for a number field `K` of degree four with its trace form
   `(x, y) ↦ Tr_{K/ℚ}(x * y)`: over `ℚ`, `H (H X) = d_K • X` with `d_K` the discriminant of `K`;
   a rational bracket-commuting map of square `-1` exists if and only if `-d_K` is a rational
   square; over `ℝ`, on the trace matrix of an integral basis, `H (H X) = (-1) ^ r₂ • X` with `r₂`
   the number of complex places.
9. `centroid_traceForm_of_root` — the example `x⁴ - x - 1`: for a number field `K` of degree four
   containing `θ` with `θ ^ 4 = θ + 1`: `H (H X) = (-283) • X`, with the unique decomposition; no
   rational bracket-commuting map has square `-1`; over `ℝ` one exists.
10. `not_lieEquiv_diagonal_of_root` — for the same `K`, the Lie algebra over `ℚ` of the trace form
    of `K` is not isomorphic to the Lie algebra over `ℚ` of the diagonal form `(1, 1, 1, -1)`,
    which does have a rational bracket-commuting map of square `-1`. The invariant is the class of
    the determinant modulo squares: `-283` against `-1`.

Controls (statement 11):

11. `controls` — (a) a number field `K` of degree four with `θ ^ 4 = θ + 1` exists; (b) for the
    degenerate diagonal form `(1, 1, 1, 0)` over `ℚ` every bracket-commuting map is `c • id`, so
    nondegeneracy cannot be dropped from statement 1; (c) the clause "not of the form `a • id`"
    cannot be dropped from statement 2(a): for the diagonal form `(1, 1, 1, -1)` over `ℚ` the
    identity is bracket-commuting with square `1`, and `1` is not `t ^ 2 * (-1)`.

Conventions.
* `IsBracketCommuting R` is `∀ X Y, R ⁅X, Y⁆ = ⁅X, R Y⁆`. It is the only definition of this file.
* `skewAdjointLieSubalgebra B` (Mathlib) is the Lie algebra of the endomorphisms `f` with
  `B (f x) y = -B x (f y)`, with the commutator bracket; `skewAdjointMatricesLieSubalgebra G`
  (Mathlib) is the Lie algebra of the square matrices `A` with `Aᵀ * G = -(G * A)`.
* `LinearMap.BilinForm.toMatrix b B` is the Gram matrix `(B (b i) (b j))` of `B` in the basis `b`;
  "`det B`" above stands for its determinant. A vector space with a basis indexed by a type with
  four elements is a four-dimensional vector space.
* `∃! ab : F × F, R = ab.1 • LinearMap.id + ab.2 • H` says that `R = a • id + c • H` for exactly
  one pair `(a, c)`.
* `NumberField.discr K` is Mathlib's discriminant of the number field `K`, an integer, read in
  `ℚ`; `Algebra.traceForm ℚ K` is the form `(x, y) ↦ Tr_{K/ℚ}(x * y)`.

Sources, by statement. The ingredients are classical (the theory of quadratic forms and of
algebras with involution). On the side of the Clifford algebra, the quadratic algebra of
statement 1 is the centre of the even Clifford algebra, `F[X]/(X² - δ)` with `δ` a representative
of the discriminant (Knus, Merkurjev, Rost, Tignol, *The Book of Involutions*, 1998, (8.10) and
(15.7)), and statement 4 corresponds to (13.2) there: a similitude is proper if and only if it
acts as the identity on that centre. These numbers are those of a pre-publication PDF of the
book; the numbering of the printed book was not confirmed. Statement 5, in dimension three and
in dimensions at least five, is stated for fields with `2 ≠ 0` and for the derived algebra, which
is `so(B)` itself from dimension three on, in D. Leijnse, arXiv:2605.26398, Theorem 2.34, as a
summary of results of N. Jacobson, *Lie Algebras*, Chapter X (Jacobson's book was not read for
this entry). In statement 8, the
discriminant of the trace form is the discriminant of the field, and its sign is `(-1) ^ r₂`
(J. S. Milne, *Algebraic Number Theory*, v3.08, p. 33 and Proposition 2.40(a)). Statements 1–4
and 8(a)–(b), which are about the Lie algebra itself, were not located as stated in the sources
read for this entry; statement 1 follows in two steps from M. Chaktoura and F. Szechtman, J. Lie
Theory 23 (2013), Theorem (`so(B) ≅ so(B|W) ⊗ F[X]/(X² - det B)`), and G. Benkart and E. Neher,
arXiv:math/0502561, Corollary 2.23(b) (`README.md`, "Relation to the literature"). Statements 2 and 7 are arithmetic in the quadratic algebra of statement 1;
statements 6, 9 and 10 are examples and statement 11 is a set of controls.

Scope.
* Fields with `2 = 0` are excluded throughout.
* Statement 4 is about the automorphisms of `so(B)` that are conjugation by a linear map
  preserving `B`. Other automorphisms of `so(B)` are not treated.
* Statements 9 and 10 are about the trace form of the field and the Lie algebra of the
  endomorphisms skew-adjoint for it.

Prior formalization (searches of 2026-11-13; `README.md`, "Prior formalization", gives files,
lines, commits and the limits of the searches). TauCeti formalizes the Clifford-algebra side: the
centre of the even Clifford algebra as `K[X]/(X² - d)`, `d` the signed discriminant, a field
exactly when `d` is not a square (`CliffordAlgebra.adjoinRootEquivCenterEven`); in dimension
four the even Clifford algebra and the Spin group over that centre; and, for the real definite
four-space, the Hodge star on two-forms as multiplication by the chirality element
(`bivectorExterior_hodgeStar`). `openai/math` has, for the real definite
form, in matrix coordinates and with no Lie algebra type, the existence clauses of statements 1
and 7(b) and the case `det g = 1` of statement 4 (`twoFormSkewAction_hodge`,
`hodgeStarFour_oriented_frame_change`). Mathlib supplies the objects under "Conventions",
`NumberField.sign_discr` and the type `so(B) →ₗ⁅F,so(B)⁆ so(B)` of Lie module morphisms, whose underlying maps are the
bracket-commuting maps; it has no declaration named for the centroid of a Lie algebra and no
centre of the even Clifford algebra. The author's entries PALOMAR-2026-10-21-000012 (the
discriminant `-283` of the field of `x⁴ - x - 1`, used in the proofs of statements 9, 10 and 11(a)) and PALOMAR-2026-09-02-000014
(the trace matrix of `ℚ[x]/(x⁴ - x - 1)`) prove facts that are not compared here. In the places
searched, no description of the bracket-commuting maps of an orthogonal Lie algebra was found
apart from the library of the author's PALOMAR-2026-11-14-000019 (same development; proved there,
not compared): a dated search result, not a statement that none exists.

Not formalized here (see also "Scope"). The Clifford algebra and the relation between `H` and its
central element; an isomorphism of `so(B)` with another Lie algebra, over any field; the
integral trace form; any group.

Proofs. Computations with matrices on Mathlib's Lie algebras of skew-adjoint endomorphisms and
matrices, not through the Clifford algebra (`README.md`, "The proofs").

Every statement here is left unproved as a placeholder; `Solution.lean` proves each, with the
identical statement and the identical definition.
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
So the bracket-commuting maps form an algebra under composition, isomorphic to `F[X]/(X² - d)`
by `X ↦ H`. The square class: for `t ≠ 0`, the operator `t • H` has (a) and (c), and (b) with `t ^ 2 * d` in place of `d`;
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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- **6. Example: Mathlib's `so' p q ℝ` outside dimension four.** Let `p` and `q` be finite types
with `card p + card q ≠ 4`, and let `R` be a bracket-commuting real-linear endomorphism of
Mathlib's `LieAlgebra.Orthogonal.so' p q ℝ` (the real matrices indexed by `p ⊕ q` that are
skew-adjoint for the diagonal form with entries `1` on `p` and `-1` on `q`). Then `R = c • id` for
some real `c`. This is the fact of statement 5 for these matrix Lie algebras. -/
theorem centroid_scalar_so' {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (h : Fintype.card p + Fintype.card q ≠ 4)
    (R : LieAlgebra.Orthogonal.so' p q ℝ →ₗ[ℝ] LieAlgebra.Orthogonal.so' p q ℝ)
    (hR : IsBracketCommuting R) : ∃ c : ℝ, R = c • LinearMap.id := by
  sorry

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
  sorry

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
`(a, c)` of real numbers. (Over `ℝ` the class of `d_K` modulo nonzero squares is its sign,
`(-1) ^ r₂`.) -/
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
  sorry

/-- **9. Example: the polynomial `x⁴ - x - 1`.** Let `K` be a number field of degree four over
`ℚ` and `θ` an element of `K` with `θ ^ 4 = θ + 1` (statement 11(a): such `K` and `θ` exist). Let
`L` be the Lie algebra over `ℚ` of the `ℚ`-linear endomorphisms of `K` that are skew-adjoint for
the trace form of `K` over `ℚ`.
(a) There is a bracket-commuting `ℚ`-linear endomorphism `H` of `L` with `H (H X) = (-283) • X`
for all `X`, such that every bracket-commuting `R` is `a • id + c • H` for exactly one pair
`(a, c)` of rational numbers.
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
  sorry

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
not a rational square. Over `ℝ` the two forms are isometric (signature `(3, 1)`), so the real Lie algebras are
isomorphic (not formalized); both have a bracket-commuting map of square `-1` (statements 9(c)
and 7(a)). -/
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
  sorry

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
  sorry

end QuaternaryCentroid
