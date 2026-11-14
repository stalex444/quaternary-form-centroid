# Bracket-commuting maps of the orthogonal Lie algebra of a quaternary form

Author: Stephanie Alexander (ORCID [0009-0003-7727-2565](https://orcid.org/0009-0003-7727-2565)).

> Draft of 2026-11-13, not submitted. Two things are the author's to settle and are marked
> `TODO (author)`: the title (the heading above is a working title; `formalization.yaml` carries a
> PROPOSED one) and her own review of the eleven statements.

Kernel-checked, in Lean 4 + Mathlib. Let `F` be a field with `2 ≠ 0`, `B` a nondegenerate
symmetric bilinear form on a four-dimensional `F`-vector space, and `so(B)` the Lie algebra of the
`B`-skew-adjoint endomorphisms. A linear map `R : so(B) → so(B)` is **bracket-commuting** when
`R ⁅X, Y⁆ = ⁅X, R Y⁆` for all `X`, `Y`; the bracket-commuting maps are what is usually called the
centroid of the Lie algebra. This repository proves that the bracket-commuting maps of `so(B)` are
the maps `a • id + c • H` for one operator `H` with `H ∘ H = det B`, a copy of the quadratic
algebra `F[X]/(X² - det B)`; that the class of `det B` modulo nonzero squares is determined by the
Lie algebra; that a linear map preserving `B` acts on `H` by its determinant; that in every other
finite dimension the bracket-commuting maps are the maps `c • id`; and what this gives over `ℝ`
and for the trace form of a number field of degree four, with the field of `x⁴ - x - 1`
(discriminant `-283`) as the instance: over `ℚ`, the Lie algebra of its trace form is not
isomorphic to the Lie algebra of the diagonal form `(1, 1, 1, -1)`.
It compares exactly eleven statements (those of `Challenge.lean`, which the registry's Comparator checks against
`Solution.lean`).

Here `det B` is the determinant of the Gram matrix of `B` in a chosen basis; it changes by a
nonzero square with the basis, and for `t ≠ 0` the operator `t • H` has square `t² · det B`. For a
diagonal form, `H` is the Hodge star of `B` on `Λ²V ≅ so(B)` taken with respect to the volume
element `e₁ ∧ e₂ ∧ e₃ ∧ e₄` of the basis, not a normalized one; this is why `H ∘ H = det B` rather
than `±1`. On skew matrices it exchanges the entries at complementary pairs of indices, with signs
and with weights from the form ("The proofs").

This entry is a formalization; nothing in it is claimed as original mathematics. The mathematics
is the classical `D₂ = A₁ × A₁` in the form it takes for the Lie algebra: `F[X]/(X² - det B)` is
the centre `Z` of the even Clifford algebra of `B`, and `so(B)` is the Lie algebra of pure
quaternions of a quaternion algebra over `Z` (*The Book of Involutions*, (8.10), (8.18),
(15.6)–(15.8)). The statements about the bracket-commuting maps themselves (1–4 and the rational
clauses of 8) were not located as stated in the sources read; statement 1 follows in two steps
from a theorem of Chaktoura and Szechtman and a corollary of Benkart and Neher ("Relation to the
literature"). The Clifford-algebra side is formalized in the Lean
library TauCeti, and the existence clauses of statements 1 and 7(b) and the case `det g = 1` of
statement 4, for the real definite form, in coordinates, in `openai/math`; see "Prior
formalization".

## Who this is for

- **Formal developments of quadratic forms and Clifford algebras.** TauCeti has the centre of the
  even Clifford algebra as `K[X]/(X² - d)` with the square criterion, and in dimension four the
  even Clifford algebra and the Spin group over that centre ("Prior formalization" names the
  files). Statements 1–4 are the corresponding statements for the Lie algebra of the form, and
  statement 5 says that for the Lie algebra, unlike for the centre of the even Clifford algebra,
  dimension four is the only dimension in which this happens. `Challenge.lean` imports Mathlib
  only, so such a development can be checked against its eleven statements.
- **Readers of the current literature in which these objects are in use.** The centre of the even
  Clifford algebra of a quaternary quadratic space and the quaternion structure over it: M. Aka,
  K. Andritsch, A. Wieser, *Planes in quadratic 4-space and associated shapes of lattices*,
  arXiv:2606.03472 (§2.1–2.2, Proposition 2.6). Centroids of simple Lie algebras, the Lie algebras
  of skew elements of algebras with involution and their centroids, and type `D₂` in degree four:
  D. Leijnse, arXiv:2605.26398 (§2.1.2, Theorem 2.34, Theorem 2.36, Lemma 3.72).
- **Trace forms of number fields.** Statement 8 uses only the class of the discriminant modulo
  rational squares. The integral trace form is a finer invariant, studied in W. Bolaños,
  G. Mantilla-Soler, *The trace form over cyclic number fields*, Canad. J. Math. 73 (2021)
  947–969, arXiv:1904.10080; G. Mantilla-Soler, C. Rivera, arXiv:1812.03133; G. Mantilla-Soler,
  arXiv:1308.2187. It is not formalized here.
- **Readers who work with arithmetic Kleinian groups**, which in the standard account come from
  quaternion algebras over a number field with exactly one complex place (J. Voight, *Quaternion
  Algebras*, author's PDF v.1.0.7u of 5 August 2026, 38.3.10, p. 708: for an order `O` of a
  quaternion algebra over a number field `F`, the group `Γ¹(O)` is a Kleinian group if and only
  if "F has exactly one complex place and B is ramified at all real places", where `B` is the
  quaternion algebra): for a rational quaternary form of negative determinant, the quadratic algebra `ℚ[X]/(X² - det B)` of statement
  1 is an imaginary quadratic field, a number field of that kind (`ℚ(√-283)` for the trace form
  of statement 9), and statement 3 says that its isomorphism class is determined by the Lie
  algebra over `ℚ`; no group is defined in this entry (statement 4 is about individual linear maps
  preserving `B`), and the entry does not say that
  its Lie algebra, or a lattice in it, is, gives or equals a Kleinian group.

## The compared statements (namespace `QuaternaryCentroid`)

`Challenge.lean` imports Mathlib only and carries one definition:
`IsBracketCommuting R := ∀ X Y, R ⁅X, Y⁆ = ⁅X, R Y⁆`, for a linear endomorphism `R` of a Lie
algebra. `skewAdjointLieSubalgebra B` (Mathlib) is the Lie algebra of the endomorphisms `f` with
`B (f x) y = -B x (f y)`; `skewAdjointMatricesLieSubalgebra G` (Mathlib) is the Lie algebra of the
square matrices `A` with `Aᵀ * G = -(G * A)`. "Dimension four" is stated as: the space has a basis
indexed by a finite type with exactly four elements, and "`det B`" is the determinant of the Gram
matrix `LinearMap.BilinForm.toMatrix b B` in that basis.

The general theorem (the lead group, statements 1–4), for a field with `2 ≠ 0` and a symmetric
nondegenerate form `B` in dimension four:

1. `centroid_of_dim_four` — there is a bracket-commuting `H` with `H (H X) = det B • X` such that
   every bracket-commuting map is `a • id + c • H` for exactly one pair `(a, c)`; and a
   bracket-commuting map that is not of the form `a • id` and has the same square is `H` or `-H`.
2. `sq_and_idempotent_iff` — (a) a bracket-commuting map, not of the form `a • id`, with square
   `c` exists if and only if `c = t² · det B` for some `t ≠ 0`; (b) a bracket-commuting map with square
   `-1`, of the form `a • id` or not, exists if and only if `-det B` or `-1` is a square (the second
   alternative is the case `a • id` with `a² = -1`); (c) a bracket-commuting idempotent other than `0` and `id` exists if and only if
   `det B` is a square; (d) two such idempotents `P`, `Q` satisfy `Q = P` or `Q = id - P`.
3. `det_eq_sq_mul_of_lieEquiv` — if `so(B)` and `so(B')` are isomorphic Lie algebras over `F`,
   then `det B' = t² · det B` for some `t ≠ 0`.
4. `isometry_conj_eq_det_smul` — for every isometry `g` of `B` (a linear map with
   `B (g x) (g y) = B x y`): `det g` is `1` or `-1`;
   conjugation by `g` is a Lie algebra equivalence `φ` of `so(B)`; and `φ ∘ H ∘ φ⁻¹ = det g • H`
   for every bracket-commuting `H`, not of the form `a • id`, whose square is a scalar. A map
   preserving `B` with determinant `-1` exists. With statement 1: conjugation by `g` fixes every
   bracket-commuting map when `det g = 1`, and is `a • id + c • H ↦ a • id - c • H` when
   `det g = -1`.

Other dimensions (statements 5–6):

5. `centroid_scalar_of_dim_ne_four` — for a nondegenerate symmetric form in any finite dimension
   other than four, every bracket-commuting map of `so(B)` is `c • id` (for a simple Lie algebra
   this is the property called central).
6. `centroid_scalar_so'` — an example of the same fact on Mathlib's matrix Lie algebras
   `LieAlgebra.Orthogonal.so' p q ℝ`: when `card p + card q ≠ 4`, every bracket-commuting map is
   `c • id`.

Corollaries and examples (statements 7–10):

7. `centroid_real_diagonal` — over `ℝ`, for a diagonal form with entries `±1` in dimension four:
   if the product of the entries is `-1` (signature `(3, 1)` or `(1, 3)`), the bracket-commuting
   maps are `a • id + c • J` with `J (J X) = -X`, a copy of `ℂ`; if the product is `1` (signature
   `(4, 0)`, `(0, 4)` or `(2, 2)`), they are `a • P + c • (id - P)` for a bracket-commuting
   idempotent `P` other than `0` and `id`, a copy of `ℝ × ℝ`. This is statements 1 and 2 over `ℝ`,
   where the class of the determinant modulo squares is its sign.
8. `centroid_traceForm` — the corollary for a number field `K` of degree four with its trace form
   `(x, y) ↦ Tr_{K/ℚ}(x y)`: over `ℚ`, `H (H X) = d_K • X` with `d_K` the discriminant of `K`, and
   every bracket-commuting map is uniquely `a • id + c • H`; a rational bracket-commuting map of
   square `-1` exists if and only if `-d_K` is a rational square; over `ℝ`, on the trace matrix of
   an integral basis, `H (H X) = (-1)^{r₂} • X` with `r₂` the number of complex places.
9. `centroid_traceForm_of_root` — an example of statement 8, the polynomial `x⁴ - x - 1`: for a
   number field `K` of degree four containing `θ` with `θ⁴ = θ + 1`: `H (H X) = (-283) • X`, with
   the unique decomposition; no rational bracket-commuting map has square `-1` (`283` is not a
   rational square); over `ℝ` one exists. The two hypotheses give `K = ℚ(θ)`, and the discriminant
   of `K` is `-283`; these two facts are used in the proof and are not compared statements of this
   entry.
10. `not_lieEquiv_diagonal_of_root` — an example of statements 2(b) and 3: for the same `K`, the
    Lie algebra over `ℚ` of the trace form of `K` is not isomorphic to the Lie algebra over `ℚ`
    of the diagonal form `(1, 1, 1, -1)`, which does have a rational bracket-commuting map of
    square `-1`. The invariant is the class of the determinant modulo rational squares: `-283`
    against `-1`. Over `ℝ` the two forms are isometric: the trace form has signature
    `(r₁ + r₂, r₂) = (3, 1)` (PALOMAR-2026-10-21-000012, `traceForm_signature`), as does
    `(1, 1, 1, -1)`. So the two real Lie algebras are isomorphic (not formalized here), and both have
    a bracket-commuting map of square `-1` (statements 9(c) and 7(a)). The obstruction is over `ℚ`.

Controls (statement 11):

11. `controls` — (a) a number field `K` of degree four with an element `θ`, `θ⁴ = θ + 1`, exists,
    so statements 9 and 10 are not vacuous; (b) for the degenerate diagonal form `(1, 1, 1, 0)`
    over `ℚ` every bracket-commuting map is `c • id`, so nondegeneracy cannot be dropped from
    statement 1; (c) the clause "not of the form `a • id`" cannot be dropped from statement 2(a):
    for the diagonal form `(1, 1, 1, -1)` over `ℚ` the identity is bracket-commuting with square
    `1`, and `1` is not `t² · (-1)`.

Three further theorems, proved from the compared statements and not compared, are in `Checks.lean`:
nondegeneracy cannot be dropped from statement 2(c) (for `(1, 1, 1, 0)` the determinant `0` is a
square and there is no bracket-commuting idempotent other than `0` and `id`); neither hypothesis on
`H` can be dropped from statement 4(c) (the conclusion fails for `id` and for `id + H`); and for
`K` as in statement 9 the Gram determinant of the trace form in every basis is `t² · (-283)`.

## The proofs

The proofs are computations with matrices; they do not go through the Clifford algebra.

- **A diagonal form.** For `η : Fin 4 → F` with nonzero entries, the skew matrices of
  `diagonal η` have the six generators `η j • E i j - η i • E j i`, and the operator is explicit:
  `X ↦ star0 (diagonal η * X) * diagonal η`, where `star0` exchanges the entries of complementary
  pairs of indices with signs (`LorentzLie.hodge`, `LorentzLie/Defs.lean`). That it commutes with
  the bracket and has square `∏ i, η i` are polynomial identities in the six coordinates; that
  every bracket-commuting map is a combination of it and the identity uses that such a map sends
  a generator into the span of that generator and its image under the operator, and that the
  elements on which two bracket-commuting maps agree are stable under every `⁅X, ·⁆`
  (`LorentzLie/Centroid.lean`; `LorentzLie.FormCentroid.hodge_description`).
- **A general form (statement 1).** For a symmetric Gram matrix `G` of nonzero determinant, the
  `G`-skew matrices are Lie-equivalent to the skew matrices of a diagonal form whose determinant
  is `t² · det G` (`LorentzLie.FormCentroid.exists_lieEquiv_etaSkew`); the description is carried
  along that equivalence (`LorentzLie.centroid_transport_field`), the operator is divided by `t`
  (`LorentzLie.exists_hodge_matrix`), and the result is carried to the endomorphisms by the matrix
  of an endomorphism in the basis (`LorentzLie.exists_hodge_of_basis`). The clause "`H` or `-H`"
  is `LorentzLie.hodge_of_basis_eq_or_eq_neg`.
- **Statement 2** is arithmetic with `a • id + c • H` and `H ∘ H = det B`
  (`LorentzLie.exists_nonscalar_sq_iff`, `LorentzLie.exists_sq_neg_one_iff`; the idempotent
  clauses in `QuaternaryCentroid/Bridge.lean`: an idempotent other than `0`, `id` is
  `½ • id + β • H` with `4 β² det B = 1`).
- **Statement 3.** The equivalence carries the operator of `B'` to a bracket-commuting map of
  `so(B)`, not of the form `a • id`, whose square is `det B'`; statement 2(a) for `B` gives
  `det B' = t² · det B` (`LorentzLie.det_toMatrix_eq_sq_mul_of_lieEquiv`).
- **Statement 4** (`QuaternaryCentroid/Bridge.lean`). Conjugation by `g` sends `H` to a
  bracket-commuting map with the same square, hence to `H` or `-H`. In an orthogonal basis, one
  matrix entry of the conjugated explicit operator is the determinant of the matrix of `g`
  (`star0_conj_entry`), which identifies the sign with `det g` (`sign_mul_det_diag`). The map of
  determinant `-1` is a reflection in a vector of an orthogonal basis.
- **Statements 5 and 6** rest on `LorentzLie.centroid_scalar_of_two_ne_zero`
  (`LorentzLie/Centroid.lean`): for a diagonal form on an index type with a number of elements
  other than four, the image of a generator commutes with everything that commutes with the
  generator, which forces it to be a multiple of the generator.
- **Statement 7** is the explicit operator for `η` with entries `±1`; for the product `1` the
  idempotent is `½ (id + H)`.
- **Statement 8** is statement 1 for the trace form in Mathlib's integral basis, whose Gram
  determinant is the discriminant by Mathlib's definition, with Mathlib's
  `NumberField.sign_discr` for the real clause (`LorentzLie/QuarticField.lean`).
- **Statements 9–11.** A number field of degree four containing a root of `x⁴ - x - 1` is
  isomorphic to the field `S₄` of the library `HermiteCompositum`, whose discriminant is `-283`
  there (`QuaternaryCentroid.Bridge.discr_of_root`). Statement 10(a): a Lie algebra equivalence
  would carry the map of 10(b) to a bracket-commuting map of square `-1` on the first Lie algebra,
  which statement 9(b) excludes.

The libraries state their theorems with `LorentzLie.IsBracketCommuting`, which has the same body as
the definition carried by the Challenge, and declare
`attribute [local instance] LieRing.ofAssociativeRing` (in Mathlib this is a definition, not a
global instance). `Challenge.lean` and `Solution.lean` declare neither an attribute nor an `open`:
every compared statement elaborates on Mathlib's default instances, and each is closed in
`Solution.lean` by one `exact`: of a single library theorem whose statement is definitionally
equal (statements 1, 2, 3, 5, 6, 7, 9), or of the tuple of the library theorems that prove its
clauses (statements 4, 8, 10, 11).

## Scope

- Fields with `2 = 0` are excluded throughout.
- Statement 4 is about the automorphisms of `so(B)` that are conjugation by a linear map
  preserving `B`. Other automorphisms of `so(B)` are not treated.
- Statements 9 and 10 are about the trace form of the field and the Lie algebra of the
  endomorphisms skew-adjoint for it.
- In statement 7 the hypothesis that every entry is `1` or `-1` is not needed (the hypothesis on
  the product makes every entry nonzero); it is kept so that the signatures can be named.
- Hypotheses that could be weakened without making a statement false, and are kept so that each
  statement stays on the case with content: in statement 3, the nondegeneracy of the two forms and
  one of the two cardinality hypotheses; in statement 4, "exactly four elements" could be "at
  least one element" (in other dimensions clause (c) is empty by statement 5); in statement 10,
  the degree hypothesis.

## Not formalized

- The Clifford algebra of the form, and the relation between `H` and its central element.
- An isomorphism of `so(B)` with another Lie algebra, over any field.
- The integral trace form of a number field.
- Any group: no orthogonal group, Spin group or arithmetic group is defined or mentioned in a
  statement.

## Relation to the literature

The sources were read on 2026-11-13; `formalization.yaml` records how each was read. The numbers
and pages quoted from *The Book of Involutions* are those of a pre-publication PDF of the book
(`https://webhomes.maths.ed.ac.uk/~v1ranick/papers/involutions.pdf`, 588 pages, cross-references
printed as "(??)"); the numbering of the printed book was not confirmed.

- **Statement 1** was not located as a stated theorem in the sources read, but it follows in two
  steps from stated results about the Lie algebra: `so(B) ≅ so(B|W) ⊗ F[X]/(X² - det B)` for a
  three-dimensional `W` on which `B` is nondegenerate (M. Chaktoura and F. Szechtman, Theorem;
  their `L(f)` is `so(B)` when `2 ≠ 0`), and `Cent(A ⊗ B) = id ⊗ Cent(B)` for a perfect `A` with
  `Cent(A) = F · id` and a unital `B` (Benkart and Neher, Corollary 2.23(b), pp. 11–12). Here
  `so(B|W)` is perfect and central (Leijnse, Theorem 2.34, type `B₁`), and the centroid of the
  commutative algebra `F[X]/(X² - det B)` is that algebra (Benkart and Neher, §2.1). It can also be
  derived from the Clifford-side results, as follows. `so(B)` is `Skew(End V, σ_b)` (Leijnse, Lemma 2.33).
  `Skew(A, σ) ≅ c(A)₀` (Knus, Merkurjev, Rost, Tignol, (8.18)). In degree four, `c(A)₀` is the
  space of pure quaternions of a quaternion algebra over `Z ≃ F[X]/(X² - disc σ)` ((15.6)–(15.8),
  (15.7), (8.10)). `disc σ_b = disc b`, which is `det b` in dimension four ((7.3)(3), §7). So `Z`
  acts on `so(B)` and commutes with the bracket. That the centroid is no larger than `Z`:
  commutativity of the centroid of a perfect algebra (Benkart and Neher, §2.1); centrality when
  `Z` is a field (Leijnse, Lemma 2.7, given there as a variant of a theorem of Jacobson's book,
  which was not read); and, in the split case, that the centroid of a product of two perfect
  algebras is the product of the centroids. This step is not stated in that form in Benkart and
  Neher's paper, but its key point is their Lemma 2.1(a), p. 3: any perfect ideal is invariant
  under the centroid (so a bracket-commuting `R` sends `A₁ = ⁅A₁, A₁⁆` into itself). Their proof
  of Lemma 2.1 refers to K. Ponomarëv (Algebra Logic 40 (2001) 365–377, Lemma 1) for a
  description of the centroid of a decomposable algebra; that paper was not read. The
  proofs here do not use this route. The Clifford-side statement itself is (8.10) and, for a
  quaternary quadratic space over a field of characteristic zero, Aka, Andritsch and Wieser,
  §2.2.
- **Statement 2** is arithmetic in `F[X]/(X² - det B)` from statement 1.
  The idempotents are written on the Clifford side by Aka, Andritsch and Wieser (§2.2, p. 9), and
  Benkart and Neher, Lemma 2.1(d), relate idempotents of the centroid to decompositions.
  Chaktoura and Szechtman report (from Bourbaki, *Lie Groups and Lie Algebras*, Ch. I, §6,
  Exercise 26; not read) that `so(B)` is the sum of two three-dimensional simple ideals when `det B`
  is a square and simple otherwise; with Benkart and Neher's Lemma 2.1(d) this is clause (c).
- **Statement 3** was not located as stated for dimension four. The nearest stated result at the
  level of Lie algebras is Leijnse, Theorem 2.36 (given there as Jacobson, Chapter X, Theorems 11
  and 12; characteristic zero), which covers types `B_l` (`l ≥ 2`) and `D_l` (`l = 3`, `l ≥ 5`)
  and as stated does not include `D₂`; with (7.3)(3) of *The Book of Involutions* it gives the same
  conclusion in even dimension 6 and at least 10 (a two-step deduction, not formalized here;
  dimension 8 is not covered by the theorem as stated). In odd dimension the conclusion fails:
  rescaling the form changes the determinant class and not the Lie algebra (*The Book of
  Involutions*, §7, p. 80). Statement 3 gives the same conclusion in dimension
  four (type `D₂`, which that theorem as stated does not include), over every field with `2 ≠ 0`,
  by a route (the bracket-commuting maps) that exists in dimension four only. Jacobson's
  Chapter X was not read. *The Book of Involutions*, Notes to Chapter IV (pp. 274–275), says that
  in characteristic 0 results of Jacobson, Chapter X, §4, on the extension of Lie algebra
  isomorphisms show directly that certain canonical Lie algebra isomorphisms of that chapter extend
  to isomorphisms of algebras with involution; whether those results cover `D₂` was not checked.
- **Statement 4**: the Clifford-side statement is (13.2), a similitude is proper if and only if the
  automorphism it induces on the Clifford algebra is the identity on the centre.
- **Statement 5** is stated, for fields of characteristic not 2 and for the derived algebra
  (equal to `so(B)` from dimension three on), in Leijnse, Theorem 2.34, given there as a summary
  of results of Jacobson's Chapter X: types `B_l` (`l ≥ 1`) and `D_l` (`l ≥ 3`). Dimensions 0, 1
  and 2 are immediate. The simplicity claims of that theorem in positive characteristic were not
  checked against a primary source; the proof here does not use them.
- **Statement 7** is statements 1 and 2 over `ℝ`. For signature `(3, 1)` it is the form taken on
  bracket-commuting maps by the textbook isomorphism of the real Lie algebras `so(3, 1)` and
  `sl(2, ℂ)` (named in Voight, §36.3, p. 658); for the other signatures, by the coincidence of types `D₂ = A₁ × A₁`
  (named in Benkart and Neher, §3.3, p. 18). Neither isomorphism is formalized here.
- **Statement 8** is statements 1 and 2 on the trace form, whose discriminant is the field
  discriminant (Milne, *Algebraic Number Theory*, v3.08, p. 33), with the sign of the discriminant
  (Proposition 2.40(a)).
- **Statement 9** is statement 8 at the discriminant `-283` (LMFDB, number field 4.2.283.1).
- Terminology. "Centroid" is the standard name (Benkart and Neher, §1). *The Book of Involutions*
  calls another object "the discriminant algebra" ((10.28), for involutions of the second kind);
  the quadratic algebra `F[X]/(X² - det B)` of this entry is not given that name here.
- Not read: N. Jacobson, *Lie Algebras* (1962), Chapter X. Also not read, and not cited as sources
  here: Knus (1991), Scharlau, Lam, Seligman.

References, with the form in which each was read (bibliographic records checked on 2026-11-13
against Crossref, the arXiv records, or the page named):

- M.-A. Knus, A. Merkurjev, M. Rost, J.-P. Tignol, *The Book of Involutions*, American
  Mathematical Society Colloquium Publications 44, 1998, doi:10.1090/coll/044.
- D. Leijnse, *Varieties admitting a holomorphic symplectic form: LLV algebras and derived
  equivalences*, arXiv:2605.26398v1 [math.AG], 26 May 2026.
- G. Benkart, E. Neher, *The centroid of extended affine and root graded Lie algebras*,
  arXiv:math/0502561v1 [math.RT], 26 February 2005 (the version read); J. Pure Appl. Algebra 205
  (2006) 117–145, doi:10.1016/j.jpaa.2005.06.007 (not opened).
- M. Chaktoura, F. Szechtman, *A note on orthogonal Lie algebras in dimension 4 viewed as current
  Lie algebras*, J. Lie Theory 23 (2013), no. 4, 1101–1103, doi:10.5802/jolt.767;
  arXiv:1306.4006v1 [math.RA] (the version read).
- M. Aka, K. Andritsch, A. Wieser, *Planes in quadratic 4-space and associated shapes of
  lattices*, arXiv:2606.03472v2 [math.NT], 17 August 2026.
- J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08, 19 July 2020,
  `https://www.jmilne.org/math/CourseNotes/ANT.pdf`.
- The LMFDB Collaboration, *The L-functions and modular forms database*, home page of the number
  field 4.2.283.1, `https://www.lmfdb.org/NumberField/4.2.283.1`, 2026 (accessed 13 November
  2026).
- J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics, Springer, 2021,
  doi:10.1007/978-3-030-56694-4. Read in the author's PDF v.1.0.7u of 5 August 2026, whose pages
  and numbering differ slightly from the printed edition; cited for one sentence of "Who this is
  for" and for the result named in the bullet on statement 7.
- W. Bolaños, G. Mantilla-Soler, *The trace form over cyclic number fields*, Canad. J. Math. 73
  (2021) 947–969, doi:10.4153/S0008414X20000255, arXiv:1904.10080.
- G. Mantilla-Soler, C. Rivera, *The integral trace form as a complete invariant for real `S_n`
  number fields*, arXiv:1812.03133; G. Mantilla-Soler, *On the Arithmetic determination of the
  trace*, arXiv:1308.2187.
- Not read: N. Jacobson, *Lie Algebras*, 1962, Chapter X (the publisher and place were not
  confirmed from a bibliographic record and are not given).

## Prior formalization

Searches of 2026-11-13. What follows is the result of a dated search, not a statement that
nothing else exists.

**Not found in any place searched:** a declaration named for the centroid of a Lie algebra, or a
description of the bracket-commuting linear maps of an orthogonal Lie algebra, apart from the
author's own: the library of PALOMAR-2026-11-14-000019, from the same development as this entry,
proves that description and does not compare it ("Relation to the author's other entries"). The maps themselves
are those underlying Mathlib's `L →ₗ⁅F,L⁆ L`, and TauCeti has Schur's lemma for irreducible Lie
modules (table below).

**TauCeti** ([`TauCetiProject/TauCeti`](https://github.com/TauCetiProject/TauCeti/tree/3602eb5f808b6a2cf7c25cf639ff8333c96f5fb9),
read at commit `3602eb5f808b6a2cf7c25cf639ff8333c96f5fb9`; lines are those of that commit; every
file below is also present at `1e668f5e55bc20f2eb87f4ba49b48833470290d1`). TauCeti formalizes the
Clifford-algebra side of this material: for a nondegenerate quadratic form in positive even
dimension over a field with `2 ≠ 0`, the centre of the even Clifford algebra is `K[X]/(X² - d)`,
`d` the signed discriminant, a field exactly when `d` is not a square (`Even/Center.lean`); in
dimension four, when that centre is a field, the even Clifford algebra is a quaternion algebra
over it and the Spin group is the norm-one group of that quaternion algebra, and when the centre
splits both are products (`Even/NonsplitCenter.lean`, `Spin/LowRank/`); `so` of the form is
Lie-equivalent to the quadratic elements of the Clifford algebra (`Quadratic/Realization.lean`);
and for the real definite four-space the Hodge star on two-forms is multiplication by the
chirality element, which is minus the volume element (`Chirality.lean`). The present entry proves
the corresponding statement for the Lie algebra itself, over any field with `2 ≠ 0`: the linear
maps of `so(B)` that commute with the bracket are `a • id + c • H` with `H ∘ H = det B`, in
dimension four, and are `c • id` in every other finite dimension (the centre of the even Clifford
algebra has dimension two in every positive even dimension). It was proved by matrix computation
on Mathlib's `skewAdjointLieSubalgebra` and imports nothing from TauCeti.

| File (under `TauCeti/`) | Declaration, line | Relation to this entry |
|---|---|---|
| `LinearAlgebra/CliffordAlgebra/Even/Center.lean` | `mem_center_even_iff_exists_eq_add_smul_volume`, 192 | Clifford-side counterpart of the exhaustion clause of statement 1. Not the same statement: elements of an associative algebra commuting with it, against linear maps of a Lie algebra commuting with its bracket. |
| same | `adjoinRootEquivCenterEven`, 347 | Clifford-side counterpart of `H ∘ H = det B`. |
| same | `isField_center_even_iff_not_isSquare_discriminant`, 365; `nonempty_center_even_algEquiv_prod_iff_isSquare_discriminant`, 378 | Clifford-side counterparts of statement 2(c). |
| same | `finrank_center_even`, 443 | The centre has dimension 2 in every positive even dimension; the bracket-commuting maps of `so(B)` have dimension 2 in dimension four only (statement 5). |
| `LinearAlgebra/CliffordAlgebra/Even/NonsplitCenter.lean` | 164 | The even Clifford algebra of a quaternary form with field centre as a quaternion algebra over it. |
| `LinearAlgebra/CliffordAlgebra/Spin/LowRank/Four.lean`, `NonsplitCenter.lean`, `SplitCenter.lean`, `QuaternionProduct.lean`, `HyperbolicFour.lean` | 88; 114; 321; 64, 184; 94, 112 | The quaternary Spin group over the centre, and as a product when the centre splits. Group level. |
| `LinearAlgebra/CliffordAlgebra/Spin/LowRank/RationalFour.lean` | 51–151 | The rational form `x² + y² + z² + 2w²`, centre `ℚ[X]/(X² - 2)`: a rational instance with nonsquare discriminant. Another form and another statement than statement 9. |
| `LinearAlgebra/CliffordAlgebra/Quadratic/Realization.lean` | `soEquivQuadratic`, 164 | The bridge between `skewAdjointLieSubalgebra` and the Clifford files; not used here. |
| `LinearAlgebra/CliffordAlgebra/Chirality.lean` | `bivectorExterior_hodgeStar`, 289; `commute_chirality_bivectorExterior`, 252; `chirality_mul_self`, 198; `chirality_eq_neg_volumeElement`, 165 | Counterpart of the existence clause of statement 1, and of the existence part of statement 7(b), at the real definite instance, on two-forms and Clifford bivectors. No exhaustion; no other field or form. |
| `Analysis/InnerProductSpace/HodgeStar/Basic.lean` | `hodgeStar_hodgeStar_of_even`, 244 | The square clause for the real definite form, on the exterior power; no bracket. |
| `LinearAlgebra/CliffordAlgebra/RealForm/Four.lean`, `Spin/Real/Four.lean`, `Spin/Real/ThreeOne.lean` | 192; 100; 79 | Real instances on the Clifford and Spin side of statement 7. |
| `LinearAlgebra/QuadraticForm/RegularFormClass/Discriminant.lean`, `Witt/Discriminant.lean` | 123, 260; 76 | The discriminant as a square class of an isometry class of forms: the form-level counterpart of statement 3. |
| `Algebra/Lie/SkewAdjoint.lean` | `skewAdjointLieEquivOfBasis`, 150 | The same equivalence as this repository's helper `LorentzLie.FormCentroid.skewAdjointEquivMatrices`, in the opposite direction, over a commutative ring. |
| `Algebra/Lie/AEval.lean` | 75 | The bracket-commuting hypothesis in use; no description of the maps that satisfy it. |
| `Algebra/Lie/Orthogonal/Killing.lean` | 116, 171 | Irreducibility of the standard module and trivial radical for at least three indices; adjacent to statement 5. |
| `Algebra/Lie/Weights/Central.lean`; `Algebra/Lie/Schur.lean` | `exists_forall_apply_eq_smul`, 137; `finrank_lieModuleHom_self`, 196 | Schur's lemma for Lie modules: over an algebraically closed field every morphism of a finite-dimensional irreducible Lie module to itself is a scalar. At the adjoint module these morphisms are the bracket-commuting maps, so this is the general tool nearest to statement 5; it was not found applied to an orthogonal Lie algebra, and statement 5 assumes neither an algebraically closed field nor irreducibility. |
| `NumberTheory/NumberField/InfinitePlace/Basic.lean` | 230 | The sign of the discriminant in parity form; not used here. |

Not found in TauCeti by these searches: a declaration named for the centroid of a Lie algebra; a description of the
bracket-commuting maps of an orthogonal Lie algebra; a Lie equivalence between an orthogonal Lie
algebra of rank four and a product; a statement about `so` of the trace form of a number field.
TauCeti's head on 2026-11-13 (`8b9f13d9936343c962096355455995c9a128af39`) was searched by file
name only: 1,219 files were added between the commit read and that head. The search has to be
repeated at the commit current on the day of submission.

**openai/math** ([`lean/OAI/Geometry/EinsteinFour`](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Geometry/EinsteinFour),
commit `4eaee87548250b2682affda7d05d947c05554bae`). The existence clauses at the real definite form,
in matrix coordinates. `CurvatureTensors02.lean`: `hodgeStarFour` (9810), `twoFormHodge_involutive` (10283),
`twoFormSkewAction_matrix` (10792), `twoFormSkewAction_hodge` (10808), `hodgeStarFour_quaternion`
(9835), `hodgeStarFour_opposite` (9840), `twoFormSkewAction_selfDual` (10819),
`twoFormSkewAction_antiSelfDual` (10823), `hodgeStarFour_oriented_frame_change` (11011);
`AngularClifford.lean`: `oppositeMatrix_commute` (66). The Hodge star on real skew `4 × 4` matrices
is involutive, commutes with the commutator action, is `±1` on two commuting quaternion triples,
and commutes with conjugation by matrices `P` with `Pᵀ P = 1`, `det P = 1`. These are counterparts
of the existence clause of statement 1, of the existence part of statement 7(b) and of the case
`det g = 1` of statement 4, for the form `(1, 1, 1, 1)`. Not found there: a Lie algebra type; a
statement that the bracket-commuting maps are exhausted; a map of determinant `-1`; any other form
or field; the discriminant. A second folder, `Geometry/TamingCompatibility`, has an involutive
Hodge star on two-forms (`DifferentialForms/StarTwoComp.lean`: `starTwo_square`, 120;
`starTwo_comp`, 31); two files of that folder were read. Limit: 1,036 files were fetched and
searched by content and three more fetched by name; the remaining files (about 162,000 of 163,097) were
searched by file name only.

**Mathlib at the pin** (`065356127b1dc0016f66b7283ce0ce2c4055aa55`) supplies
`skewAdjointLieSubalgebra`, `skewAdjointMatricesLieSubalgebra`, `LieAlgebra.Orthogonal.so'`,
`LinearMap.BilinForm.toMatrix`, `NumberField.discr`, `Algebra.traceForm`, and
`NumberField.sign_discr` (used for statement 8(c)). It has no declaration named for the
centroid of a Lie algebra (`centroid` does not occur under `Mathlib/Algebra/Lie`; `CentroidHom` is
for non-associative rings and is not used here); the bracket-commuting maps of `L` are the linear
maps underlying its Lie module morphisms `L →ₗ⁅F,L⁆ L` (`LieModuleHom`, whose field `map_lie'` is
the equation of `IsBracketCommuting`), and no description of that space for an orthogonal Lie
algebra was found there. It has no centre of the even Clifford algebra, and
`exteriorPower.hodgeStar` with its square identity as a TODO of that file.

**Other Lean libraries searched:** `leanprover-community/physlib`
(`76e1b4f0171d27a0d35334a633263a40ecf24fd5`), `facebookresearch/atlas-lean`
(`f83e3b9054234d1c0f6455272c774f4559b44522`), `xiyin137/OSreconstruction`
(`cf0904e34a7c146a9f312f601e3707dca4a87697`, 40 files and file names) and the Yang–Mills release
`yang-mills-group/OpenAI-YM-20261028` (`3456e5e75cf8d4cd558955a5c7638fba2d68f464`): nothing
related to these statements was found.
physlib's `lorentzAlgebra` is defined on `LieAlgebra.Orthogonal.so' (Fin 1) (Fin 3) ℝ`
(`Physlib/Relativity/LorentzAlgebra/Basic.lean:30`), the cardinality that statement 6 excludes.

**Outside Lean:** Isabelle AFP (the 1,054 entry ids of the site map, matched against `clifford`,
`quadratic`, `orthogonal`, `discrimin`, `hodge`, `exterior`, `lie`, `centr`; ids only), Coq (the
file tree of `math-comp/math-comp` and its `algebra/sesquilinear.v`; no other Coq repository), HOL
Light (`Multivariate/clifford.ml` and four files under `Geometric_Algebra/` and `Quaternions/`) and
Metamath (`set.mm`, by term): no centroid of an orthogonal Lie algebra, no quadratic algebra of a
quaternary form and no centre of the even Clifford algebra was found by these searches.

## Relation to the author's other entries

For the registered entries, the commits below are those of the registry's public records; every
commit below was checked against the public repository on 2026-11-13 and again on 2026-11-14.

- **PALOMAR-2026-10-21-000012**
  ([`stalex444/pdt-hermite-signature-compositum`](https://github.com/stalex444/pdt-hermite-signature-compositum/tree/5aa870e98236ba240561b798265c629df8c2d031)).
  Its compared statement `integral_structure` proves `discr S₄ = -283` for the field `S₄`
  generated by a root of `x⁴ - x - 1`. Three modules of its library `HermiteCompositum` (`Defs`,
  `Port014`, `Instance`) are copied here byte for byte and used on the Solution side only, in the
  proofs of statements 9, 10 and 11(a). The value `-283` is not claimed again: in statement 9 it
  appears as the square of `H`.
- **PALOMAR-2026-09-02-000014**
  ([`stalex444/golden-family-trace-forms`](https://github.com/stalex444/golden-family-trace-forms/tree/9528df064df58318213b541048e05ff4c0d9cb67)).
  Its compared statements `traceMatrix_quartic` and `discr_quartic` give the trace matrix of
  `ℚ[x]/(x⁴ - x - 1)` in the power basis and the discriminant `-283` of that basis. The same matrix
  is `traceGram` in `LorentzLie/FormDefs.lean`. No compared statement here states the Gram matrix.
- **PALOMAR-2026-10-14-000009**
  ([`stalex444/pdt-em-source-selection`](https://github.com/stalex444/pdt-em-source-selection/tree/1c9ba637b5e664a88b6487d463515587616476e1)).
  `GravityScreening/SignedLieGeneration.lean` is byte-identical to the file of the same path
  there (at the commits of both registered versions); one definition of it is used (`skew`).
- **PALOMAR-2026-09-30-000024**
  ([`stalex444/pdt-hodge-lie-generation`](https://github.com/stalex444/pdt-hodge-lie-generation/tree/e2d8dde6f076b730b9a718c95ff1664c6aa88b51)).
  Its `Challenge.lean` defines, in coordinates, the operator `H` of this entry at the form
  `(1, 1, 1, -1)`, extended by zero to `15 × 15` matrices (`integralHodge`, line 72;
  `geometricHodge`, line 84). Its one compared statement is about the Lie algebra `sl(15, K)`
  generated by that operator and fifteen adjoint actions, and about the linear maps of
  `sl(15, K)` commuting with the commutator actions of those sixteen matrices. No statement is
  shared with this entry.
- **A public repository that is not a registered entry:**
  [`stalex444/one-complex-place-lorentz-group-galois-boost`](https://github.com/stalex444/one-complex-place-lorentz-group-galois-boost/tree/ec70bded79e51b31f907b085f71756a79df0fe33).
  Its `Challenge.lean` defines, through six coordinates, an operator `hodgeOp` on real `4 × 4`
  matrices for the form `(1, 1, 1, -1)`, and its statement `hodge_exchange` (line 466) computes
  that operator on one family of matrices. The development from which this entry is taken proves
  that `hodgeOp` is the operator of this entry at that form; that theorem is not in this
  repository (`BUILD.txt`, "The cut in LorentzLie/Defs.lean"). No statement there is about
  bracket-commuting maps.
- **PALOMAR-2026-11-14-000019**
  ([`stalex444/minkowski-lorentz-algebra`](https://github.com/stalex444/minkowski-lorentz-algebra/tree/91aee70f9daddadda2f97f4694b9b4352430ecba)).
  Its main theorem (statement 6 there): every invariant bilinear form on `so(3, 1)` is
  `a · tr(XY) + b · tr(H(X) Y)` for exactly one pair `(a, b)`. It is proved from the description
  of the bracket-commuting maps at the Minkowski form, and that entry refers to this one, as an
  entry in preparation, for the description. Its other compared statements include the
  isomorphism with `sl(2, ℂ)` as a real Lie algebra (statements 1–2 there); a bracket-commuting
  `H` with `H ∘ H = -1` that the isomorphism carries to multiplication by `-i` (statement 4 there:
  the existence part of statement 7(a) here, at one form); the exponential criterion; the
  complexification; and `so(4)`, `so(2, 2)` as products (statement 7 there, on the Lie algebras
  of statement 7(b) here). Its library proves, without comparing them, versions of the library
  theorems from which statements 1, 2(a)–(b), 3, 5, 6 and 7 here are proved
  (`LorentzLie/FormCentroid.lean`: `exists_hodge_of_basis`, `hodge_of_basis_eq_or_eq_neg`,
  `exists_nonscalar_sq_iff`, `exists_sq_neg_one_iff`, `det_toMatrix_eq_sq_mul_of_lieEquiv`,
  `centroid_scalar_of_basis`; `LorentzLie/Centroid.lean`: `centroid_scalar_so'`,
  `hodge_centroid_real`). Both libraries come from the same unpublished development; only
  `GravityScreening/SignedLieGeneration.lean` is byte-identical. The statement that every
  bracket-commuting map is `a • id + c • H` with `H ∘ H = det B` is compared in this entry only.

## Layout

| Path | What it is |
|---|---|
| `Challenge.lean` | The eleven statements with placeholders, and the one definition. Imports Mathlib only. |
| `Solution.lean` | The same definition and statements, each proved by one `exact`. Generated from `Challenge.lean` by a script kept outside the repository. |
| `QuaternaryCentroid/Bridge.lean` | Helper theorems for the compared statements (namespace `QuaternaryCentroid.Bridge`), including the proofs written for this entry: statement 4, statement 2(c)–(d), statement 7(b). |
| `LorentzLie/Defs.lean`, `Centroid.lean`, `FormDefs.lean`, `FormCentroid.lean`, `QuarticField.lean` | The proof library (namespace `LorentzLie`). |
| `GravityScreening/SignedLieGeneration.lean` | One module from an earlier development of the author's; `LorentzLie/Defs.lean` uses its definition `skew`. |
| `HermiteCompositum/Defs.lean`, `Port014.lean`, `Instance.lean` | Three modules of the library of PALOMAR-2026-10-21-000012, byte for byte. |
| `Checks.lean` | Three theorems proved from the compared statements; not compared. |
| `Axioms.lean` | `#print axioms` for the compared statements, the checks and the main library theorems; not a build target. |
| `BUILD.txt`, `SHA256SUMS` | The build record and file hashes. |

**Names.** The proof library keeps the namespace and module names it has in the author's
unpublished development from which it is taken: `LorentzLie`, `GravityScreening`,
`HermiteCompositum`. They were not renamed, because renaming would change the names of the
declarations that were reviewed. `LorentzLie` refers to the Lie algebra of a form of signature `(3, 1)`,
the Lorentz Lie algebra: it is the case of statement 7(a) and of the diagonal form `(1, 1, 1, -1)`
of statement 10. Every statement of the entry is a mathematical statement; no physical
identification is stated. The operator `H` is called `hodge` in the library because for a diagonal form it is the
Hodge star on skew matrices, taken with respect to the volume element `e₁ ∧ e₂ ∧ e₃ ∧ e₄` of the
basis (not normalized; hence `H ∘ H = det B`).

**Departures from the development's files** (`BUILD.txt` has the diffs and the checks).
`LorentzLie/FormDefs.lean` is byte-identical to the development's file. `LorentzLie/Defs.lean` is
the development's file without two sections: one compared its operator with an operator of a
library that is not part of this entry (with the two imports of that library), and one defined
matrices for statements of the development that are not in this repository; the two bullets of
its opening docstring that described them were removed. In `LorentzLie/Centroid.lean`,
`FormCentroid.lean` and `QuarticField.lean`, working labels of the development were removed from
docstrings and section headings, and `QuarticField.lean` imports `HermiteCompositum.Instance`
where the development imports a larger module of that library. No declaration changed: the type
and the value of every remaining declaration have the same hash before and after.

**The three `HermiteCompositum` modules** are not edited, so their docstrings are those of the
registered entry and refer to that entry's own files: where they say `Challenge.lean` or
`Solution.lean` they mean that entry's, they number that entry's compared statements, and they name
three modules of that library which are not copied here: `Hermite.lean` (line 33 of
`HermiteCompositum/Defs.lean`), `Squarefree.lean` (line 180 of `HermiteCompositum/Instance.lean`)
and `Places` (lines 363 and 370 of the same file); all three are in the repository of
PALOMAR-2026-10-21-000012.

## Build

Lean `v4.35.0-rc2`, Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55` (`lean-toolchain`,
`lake-manifest.json`).

```
lake exe cache get
lake build
lake env lean Axioms.lean
```

`lake build` builds the libraries, `Challenge`, `Solution` and `Checks`; the only warnings are the
eleven placeholders of `Challenge.lean` a deprecation warning in one copied module (`GravityScreening/SignedLieGeneration.lean`) and
linter warnings in another (`HermiteCompositum/Port014.lean`). Every compared
statement depends on the axioms `propext`, `Classical.choice`, `Quot.sound` only. `BUILD.txt`
records the build, the axioms, the comparison of the statements of `Challenge.lean` and
`Solution.lean`, and a local run of the registry's Comparator.

## Authorship, production and licence

Author: Stephanie Alexander (ORCID [0009-0003-7727-2565](https://orcid.org/0009-0003-7727-2565)).
The Lean was developed with AI assistance (Anthropic Claude, in Claude Code) under the author's
direction. The statements were reviewed by separate AI sessions, with compiled probe files and an
independent exact computation; the builds, the checks of `BUILD.txt` and a local run of the
registry's Comparator were made on the author's machine. `formalization.yaml` (`automation`,
`review`) gives the account. The library modules (`LorentzLie/`) were written on 2026-11-12,
before the sources were read. The proofs in `QuaternaryCentroid/Bridge.lean` (statement 4,
statement 2(c)–(d), statement 7(b)) were written on 2026-11-13, when the report of the search for
sources and prior formalizations was in hand. TODO (author): her own review of the eleven statements is not yet
recorded.

Licence: MIT (`LICENSE`). The repository contains no text of another project: the Challenge
imports Mathlib only and carries one definition, written for this entry; the copied modules are
the author's own, the `LorentzLie` modules from her unpublished development and the others from
her public repositories named above, which are under the MIT licence.
