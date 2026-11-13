module
public import Mathlib
public import HermiteCompositum.Hermite
public import HermiteCompositum.TraceSignature
public import HermiteCompositum.Places
public import HermiteCompositum.TraceProjection
public import HermiteCompositum.Port014
public import HermiteCompositum.Instance
public import HermiteCompositum.Extras

@[expose] public section
/-!
# Assembly: the instance-level compared statements on the concrete tower

Nothing here is re-proved: every theorem is a general theorem of this package (`Hermite`,
`TraceSignature`, `Places`, `TraceProjection`, `Extras`) applied to the concrete tower of `Instance`
`K₃ = ℚ[X]/(X³ − X − 1)`, `L = K₃[Y]/(Y⁴ − Y − 1)`, `S₃ = ℚ⟮ρ⟯`, `S₄ = ℚ⟮Q⟯`, with the hypotheses
the general files leave open discharged by name.

Compared statements closed here (numbering as in `Challenge.lean`):
* (10) **places and trace-form type.** `(r₁, r₂) = (1, 1)` for `S₃`, `(2, 1)` for `S₄`,
  `(2, 5)` for `L`; the trace form `Tr_{L/ℚ}(x²)` has type `(7, 5)`.
  Route: the theorem of `TraceSignature` (statement 2) read backwards on the ported Hankel signatures
  `(2, 1)` and `(3, 1)` of 000014 gives the sector place counts — **no root is located**, the
  count is `r₂ = sigNeg` — then the product formula of `Places` (statement 3) gives `(2, 5)` for `L`,
  then `TraceSignature` again gives `(7, 5)`. This is a second kernel derivation of the type `(7, 5)`,
  independent of the registered entry 000014's route (a Kronecker product of the two sector
  Sylvester forms); the two agree.
* (13) **orthogonal decomposition types.** `L = S₃ ⊕ S₃^⊥` and `L = S₄ ⊕ S₄^⊥` for
  `Tr_{L/ℚ}(xy)`; the form restricts to `4 · Tr_{S₃}` (type `(2, 1)`) and to `3 · Tr_{S₄}` (type
  `(3, 1)`); the transverse forms on `S₃^⊥ = ker Tr_{L/S₃}` and `S₄^⊥ = ker Tr_{L/S₄}` have
  types `(5, 4)` and `(4, 4)` — statement 5 of `TraceProjection` with its four signature hypotheses
  discharged by `TraceSignature`.
* (9) **signed discriminant.** `discr L = (−23)⁴ · (−283)³ = −6342648595267`, from the
  signed compositum theorem of `Places` (statement 4) on the sector data of `Instance`; the two
  hypothesis-form corollaries of `Instance` are discharged as cross-checks.
* (5) **transverse type, unconditional.** The transverse-type theorem of `TraceProjection` with its four signature hypotheses
  discharged by `TraceSignature`, for every number field and every subfield
  (`transverseForm_signature_unconditional`).
* (14) **covolume.** `covol(𝓞 L) = 2⁻⁵ · 23² · 283 · √283` in Mathlib's mixed space, and the
  normalization made explicit: it is `4 · covol(𝓞 S₃)⁴ · covol(𝓞 S₄)³`.
* (15) **minimal polynomial and index.** `minpoly ℚ (ρQ) = rulerPolyQ` (the ruler polynomial) is proved here — an
  ideal-membership certificate for `rulerPoly(ρQ) ∈ (ρ³ − ρ − 1, Q⁴ − Q − 1)` plus
  `ℚ⟮ρQ⟯ = L` from the subfield lattice of `Extras` — so the index theorem of `Extras` gives
  `[𝓞 L : ℤ[ρQ]] = 53` on the concrete field.
* (16)–(18) **instantiated.** The subfield lattice `{ℚ, S₃, S₄, L}`, root-rigidity, circle-freeness
  and the Smyth-floor statement (Smyth cited as a hypothesis, as in `Extras`) on the concrete `L`.
-/

open Polynomial NumberField NumberField.InfinitePlace IntermediateField Module

namespace HermiteCompositum.Assembly

open HermiteCompositum.Instance

/-! ### The two root relations in `L` (the abstract data of `Extras`) -/

/-- `ρ³ − ρ − 1 = 0` in `L`. -/
theorem ρ_cubic : ρ ^ 3 - ρ - 1 = 0 := by
  have h := aeval_ρ
  simp only [Port014.fρ, map_sub, map_pow, map_one, aeval_X] at h
  exact h

/-- `Q⁴ − Q − 1 = 0` in `L`. -/
theorem Q_quartic : Q ^ 4 - Q - 1 = 0 := by
  have h := aeval_Q
  simp only [Port014.fQ, map_sub, map_pow, map_one, aeval_X] at h
  exact h

theorem ρ_ne_zero : ρ ≠ 0 := by
  intro h0
  have h := ρ_cubic
  rw [h0] at h
  norm_num at h

theorem Q_ne_zero : Q ≠ 0 := by
  intro h0
  have h := Q_quartic
  rw [h0] at h
  norm_num at h

/-! ### (10a) The sector place counts from the ported Hankel signatures, via `TraceSignature`

The ported forms `Port014.qTraceρ`, `Port014.qTraceQ` are the trace forms of
`ℚ[X]/(X³ − X − 1)`, `ℚ[X]/(X⁴ − X − 1)`; the `ℚ`-algebra equivalences `e₃`, `e₄` of `Instance` carry
them isometrically onto the trace forms of `S₃`, `S₄`. -/

/-- The ported cubic trace form is isometric to the trace form of `S₃` through `e₃`. -/
noncomputable def traceFormIsometry₃ :
    Port014.qTraceρ.IsometryEquiv (Algebra.traceForm ℚ S₃).toQuadraticMap where
  toLinearEquiv := e₃.toLinearEquiv
  map_app' x := by
    change (Algebra.traceForm ℚ S₃).toQuadraticMap (e₃ x) = Port014.qTraceρ x
    rw [Port014.qTraceρ_apply, LinearMap.BilinMap.toQuadraticMap_apply, Algebra.traceForm_apply,
      ← map_mul, Algebra.trace_eq_of_algEquiv]

/-- The ported quartic trace form is isometric to the trace form of `S₄` through `e₄`. -/
noncomputable def traceFormIsometry₄ :
    Port014.qTraceQ.IsometryEquiv (Algebra.traceForm ℚ S₄).toQuadraticMap where
  toLinearEquiv := e₄.toLinearEquiv
  map_app' x := by
    change (Algebra.traceForm ℚ S₄).toQuadraticMap (e₄ x) = Port014.qTraceQ x
    rw [Port014.qTraceQ_apply, LinearMap.BilinMap.toQuadraticMap_apply, Algebra.traceForm_apply,
      ← map_mul, Algebra.trace_eq_of_algEquiv]

/-- The trace form of `S₃` has type `(2, 1)` (the ported Hankel signature of 000014). -/
theorem traceForm_type_S₃ :
    sigPos (Algebra.traceForm ℚ S₃).toQuadraticMap = 2 ∧
      sigNeg (Algebra.traceForm ℚ S₃).toQuadraticMap = 1 := by
  have e : QuadraticMap.Equivalent Port014.qTraceρ (Algebra.traceForm ℚ S₃).toQuadraticMap :=
    ⟨traceFormIsometry₃⟩
  rw [← e.sigPos_eq, ← e.sigNeg_eq]
  exact Port014.traceForm_signature_ρ

/-- The trace form of `S₄` has type `(3, 1)` (the ported Hankel signature of 000014). -/
theorem traceForm_type_S₄ :
    sigPos (Algebra.traceForm ℚ S₄).toQuadraticMap = 3 ∧
      sigNeg (Algebra.traceForm ℚ S₄).toQuadraticMap = 1 := by
  have e : QuadraticMap.Equivalent Port014.qTraceQ (Algebra.traceForm ℚ S₄).toQuadraticMap :=
    ⟨traceFormIsometry₄⟩
  rw [← e.sigPos_eq, ← e.sigNeg_eq]
  exact Port014.traceForm_signature_Q

/-- `r₂(S₃) = 1`: `sigNeg_traceForm` read backwards (`r₂ = sigNeg`) on the ported signature. No root of
`x³ − x − 1` is located. -/
theorem nrComplexPlaces_S₃ : nrComplexPlaces S₃ = 1 := by
  rw [← sigNeg_traceForm S₃, traceForm_type_S₃.2]

/-- `r₁(S₃) = 1`: from `r₁ + r₂ = sigPos = 2`. -/
theorem nrRealPlaces_S₃ : nrRealPlaces S₃ = 1 := by
  have h := sigPos_traceForm S₃
  rw [traceForm_type_S₃.1, nrComplexPlaces_S₃] at h
  omega

/-- `r₂(S₄) = 1`: `sigNeg_traceForm` read backwards on the ported signature `(3, 1)`. -/
theorem nrComplexPlaces_S₄ : nrComplexPlaces S₄ = 1 := by
  rw [← sigNeg_traceForm S₄, traceForm_type_S₄.2]

/-- `r₁(S₄) = 2`: from `r₁ + r₂ = sigPos = 3`. -/
theorem nrRealPlaces_S₄ : nrRealPlaces S₄ = 2 := by
  have h := sigPos_traceForm S₄
  rw [traceForm_type_S₄.1, nrComplexPlaces_S₄] at h
  omega

/-! ### (10b) The place counts of `L`, via `Places` -/

/-- `(r₁, r₂)(L) = (2, 5)`: statement 3 (`Places`) on the sector counts `(1, 1)` and `(2, 1)`. -/
theorem places_L : nrRealPlaces L = 2 ∧ nrComplexPlaces L = 5 :=
  places_compositum_of_one_one_two_one S₃_linearDisjoint_S₄ S₃_sup_S₄
    nrRealPlaces_S₃ nrComplexPlaces_S₃ nrRealPlaces_S₄ nrComplexPlaces_S₄

theorem nrRealPlaces_L : nrRealPlaces L = 2 := places_L.1

theorem nrComplexPlaces_L : nrComplexPlaces L = 5 := places_L.2

/-! ### (10c) The trace-form type of `L`, via `TraceSignature` again -/

/-- **The trace form of `L` has type `(7, 5)`.** This is a second kernel derivation of the
type, independent of the registered entry 000014 (whose route is the Kronecker product of the
two sector Sylvester forms): here it is the trace-form signature theorem of `TraceSignature`
(statement 2) on the place counts `(2, 5)`, which themselves come from that theorem read backwards
on the sector Hankel signatures and the product formula of `Places`. No root location enters anywhere. -/
theorem traceForm_type_L :
    sigPos (Algebra.traceForm ℚ L).toQuadraticMap = 7 ∧
      sigNeg (Algebra.traceForm ℚ L).toQuadraticMap = 5 := by
  rw [sigPos_traceForm, sigNeg_traceForm, nrRealPlaces_L, nrComplexPlaces_L]
  exact ⟨rfl, rfl⟩

/-- **Statement (10), bundled**: places and trace-form type of the sectors and of `L`. -/
theorem places_and_type :
    (nrRealPlaces S₃ = 1 ∧ nrComplexPlaces S₃ = 1) ∧
      (nrRealPlaces S₄ = 2 ∧ nrComplexPlaces S₄ = 1) ∧
      (nrRealPlaces L = 2 ∧ nrComplexPlaces L = 5) ∧
      (sigPos (Algebra.traceForm ℚ L).toQuadraticMap = 7 ∧
        sigNeg (Algebra.traceForm ℚ L).toQuadraticMap = 5) :=
  ⟨⟨nrRealPlaces_S₃, nrComplexPlaces_S₃⟩, ⟨nrRealPlaces_S₄, nrComplexPlaces_S₄⟩, places_L,
    traceForm_type_L⟩

/-! ### (9) The signed discriminant, via `Places` -/

/-- **Statement (9)**: `discr L = (−23)⁴ · (−283)³`, the signed compositum theorem of `Places` on the
sector discriminants and degrees of `Instance`. -/
theorem discr_L_signed : discr L = (-23) ^ 4 * (-283) ^ 3 :=
  discr_compositum_eq S₃_linearDisjoint_S₄ S₃_sup_S₄ discr_S₃ discr_S₄ finrank_S₃ finrank_S₄
    (by norm_num)

/-- **Statement (9), the numeral**: `discr L = −6342648595267`. -/
theorem discr_L : discr L = -6342648595267 := by
  rw [discr_L_signed, neg_twentythree_pow_four_mul_neg_283_pow_three]

/-- Cross-check: the hypothesis-form corollary of `Instance` via `sign_discr`, discharged by
`nrComplexPlaces_L`. -/
theorem discr_L_via_sign : discr L = -(23 ^ 4 * 283 ^ 3) :=
  discr_L_of_nrComplexPlaces nrComplexPlaces_L

/-- Cross-check: the hypothesis-form corollary of `Instance` via the signed compositum identity,
discharged by `discr_compositum` (`Places`) on `isCoprime_discr`. -/
theorem discr_L_via_compositum : discr L = (-23) ^ 4 * (-283) ^ 3 :=
  discr_L_of_signed_compositum (discr_compositum S₃_linearDisjoint_S₄ S₃_sup_S₄ isCoprime_discr)

/-! ### (5c) hypothesis-free: the transverse-type theorem with the trace-form signatures -/

/-- **Compared statement (5c), unconditional.** `transverseForm_signature` (`TraceProjection`) carries the
four trace-form signature values of `E` and `F` as explicit hypotheses (so that `TraceProjection`
does not depend on `TraceSignature`); `TraceSignature` proves exactly those values for every number field, so the general
statement holds with no hypothesis at all: for every number field `E` and every subfield `F`, the
restriction of `Tr_{E/ℚ}(x²)` to `ker Tr_{E/F}` has `sigPos = r₁(E) + r₂(E) − r₁(F) − r₂(F)` and
`sigNeg = r₂(E) − r₂(F)`. -/
theorem transverseForm_signature_unconditional {E : Type*} [Field E] [NumberField E]
    (F : IntermediateField ℚ E) :
    sigPos (transverseForm F) =
        nrRealPlaces E + nrComplexPlaces E - nrRealPlaces F - nrComplexPlaces F ∧
      sigNeg (transverseForm F) = nrComplexPlaces E - nrComplexPlaces F :=
  transverseForm_signature F (sigPos_traceForm E) (sigNeg_traceForm E)
    (sigPos_traceForm F) (sigNeg_traceForm F)

/-! ### (13) Orthogonal decompositions of `L` for `Tr_{L/ℚ}(xy)`, via `TraceProjection` -/

theorem finrank_S₃_L : Module.finrank S₃ L = 4 := by
  have h := Module.finrank_mul_finrank ℚ S₃ L
  rw [finrank_S₃, finrank_L] at h
  omega

theorem finrank_S₄_L : Module.finrank S₄ L = 3 := by
  have h := Module.finrank_mul_finrank ℚ S₄ L
  rw [finrank_S₄, finrank_L] at h
  omega

/-- `L = S₃ ⊕ S₃^⊥` for the trace form. -/
theorem isCompl_S₃_orthogonal :
    IsCompl (Subalgebra.toSubmodule S₃.toSubalgebra)
      ((Algebra.traceForm ℚ L).orthogonal (Subalgebra.toSubmodule S₃.toSubalgebra)) :=
  isCompl_orthogonal_rat S₃

/-- `L = S₄ ⊕ S₄^⊥` for the trace form. -/
theorem isCompl_S₄_orthogonal :
    IsCompl (Subalgebra.toSubmodule S₄.toSubalgebra)
      ((Algebra.traceForm ℚ L).orthogonal (Subalgebra.toSubmodule S₄.toSubalgebra)) :=
  isCompl_orthogonal_rat S₄

/-- `S₃^⊥ = ker Tr_{L/S₃}`. -/
theorem orthogonal_S₃_eq_ker :
    (Algebra.traceForm ℚ L).orthogonal (Subalgebra.toSubmodule S₃.toSubalgebra) =
      LinearMap.ker ((Algebra.trace S₃ L).restrictScalars ℚ) :=
  orthogonal_eq_ker_trace_rat S₃

/-- `S₄^⊥ = ker Tr_{L/S₄}`. -/
theorem orthogonal_S₄_eq_ker :
    (Algebra.traceForm ℚ L).orthogonal (Subalgebra.toSubmodule S₄.toSubalgebra) =
      LinearMap.ker ((Algebra.trace S₄ L).restrictScalars ℚ) :=
  orthogonal_eq_ker_trace_rat S₄

/-- The trace form of `L` restricted to `S₃` is `4 · Tr_{S₃/ℚ}(x²)` ((5b) of `TraceProjection` as forms,
with `[L : S₃] = 4`). -/
theorem restrict_S₃_equivalent :
    QuadraticMap.Equivalent
      ((Algebra.traceForm ℚ L).toQuadraticMap.restrict (Subalgebra.toSubmodule S₃.toSubalgebra))
      ((4 : ℚ) • (Algebra.traceForm ℚ S₃).toQuadraticMap) := by
  have e : QuadraticMap.Equivalent
      ((Algebra.traceForm ℚ L).toQuadraticMap.restrict (Subalgebra.toSubmodule S₃.toSubalgebra))
      ((Module.finrank S₃ L : ℚ) • (Algebra.traceForm ℚ S₃).toQuadraticMap) :=
    ⟨restrictTraceFormIsometryEquiv S₃⟩
  have h : ((Module.finrank S₃ L : ℕ) : ℚ) = 4 := by rw [finrank_S₃_L]; norm_num
  rwa [h] at e

/-- The trace form of `L` restricted to `S₄` is `3 · Tr_{S₄/ℚ}(x²)`. -/
theorem restrict_S₄_equivalent :
    QuadraticMap.Equivalent
      ((Algebra.traceForm ℚ L).toQuadraticMap.restrict (Subalgebra.toSubmodule S₄.toSubalgebra))
      ((3 : ℚ) • (Algebra.traceForm ℚ S₄).toQuadraticMap) := by
  have e : QuadraticMap.Equivalent
      ((Algebra.traceForm ℚ L).toQuadraticMap.restrict (Subalgebra.toSubmodule S₄.toSubalgebra))
      ((Module.finrank S₄ L : ℚ) • (Algebra.traceForm ℚ S₄).toQuadraticMap) :=
    ⟨restrictTraceFormIsometryEquiv S₄⟩
  have h : ((Module.finrank S₄ L : ℕ) : ℚ) = 3 := by rw [finrank_S₄_L]; norm_num
  rwa [h] at e

/-- The restriction to `S₃` has type `(2, 1)`. -/
theorem restrict_S₃_type :
    sigPos ((Algebra.traceForm ℚ L).toQuadraticMap.restrict
        (Subalgebra.toSubmodule S₃.toSubalgebra)) = 2 ∧
      sigNeg ((Algebra.traceForm ℚ L).toQuadraticMap.restrict
        (Subalgebra.toSubmodule S₃.toSubalgebra)) = 1 := by
  rw [sigPos_restrict_subfield, sigNeg_restrict_subfield]
  exact traceForm_type_S₃

/-- The restriction to `S₄` has type `(3, 1)`. -/
theorem restrict_S₄_type :
    sigPos ((Algebra.traceForm ℚ L).toQuadraticMap.restrict
        (Subalgebra.toSubmodule S₄.toSubalgebra)) = 3 ∧
      sigNeg ((Algebra.traceForm ℚ L).toQuadraticMap.restrict
        (Subalgebra.toSubmodule S₄.toSubalgebra)) = 1 := by
  rw [sigPos_restrict_subfield, sigNeg_restrict_subfield]
  exact traceForm_type_S₄

/-- **The transverse form on `S₃^⊥ = ker Tr_{L/S₃}` has type `(5, 4)`**: (5c) of `TraceProjection` with
its four signature hypotheses discharged by `TraceSignature`. -/
theorem transverse_S₃_type :
    sigPos (transverseForm S₃) = 5 ∧ sigNeg (transverseForm S₃) = 4 := by
  have h := transverseForm_signature S₃ (sigPos_traceForm L) (sigNeg_traceForm L)
    (sigPos_traceForm S₃) (sigNeg_traceForm S₃)
  rw [nrRealPlaces_L, nrComplexPlaces_L, nrRealPlaces_S₃, nrComplexPlaces_S₃] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨by omega, by omega⟩

/-- **The transverse form on `S₄^⊥ = ker Tr_{L/S₄}` has type `(4, 4)`** — the complement of the
quartic sector is neutral. -/
theorem transverse_S₄_type :
    sigPos (transverseForm S₄) = 4 ∧ sigNeg (transverseForm S₄) = 4 := by
  have h := transverseForm_signature S₄ (sigPos_traceForm L) (sigNeg_traceForm L)
    (sigPos_traceForm S₄) (sigNeg_traceForm S₄)
  rw [nrRealPlaces_L, nrComplexPlaces_L, nrRealPlaces_S₄, nrComplexPlaces_S₄] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨by omega, by omega⟩

/-- The same type `(5, 4)` read on the orthogonal complement `S₃^⊥` itself. -/
theorem orthogonal_S₃_type :
    sigPos ((Algebra.traceForm ℚ L).toQuadraticMap.restrict
        ((Algebra.traceForm ℚ L).orthogonal (Subalgebra.toSubmodule S₃.toSubalgebra))) = 5 ∧
      sigNeg ((Algebra.traceForm ℚ L).toQuadraticMap.restrict
        ((Algebra.traceForm ℚ L).orthogonal (Subalgebra.toSubmodule S₃.toSubalgebra))) = 4 := by
  rw [orthogonal_S₃_eq_ker]
  exact transverse_S₃_type

/-- The same type `(4, 4)` read on the orthogonal complement `S₄^⊥` itself. -/
theorem orthogonal_S₄_type :
    sigPos ((Algebra.traceForm ℚ L).toQuadraticMap.restrict
        ((Algebra.traceForm ℚ L).orthogonal (Subalgebra.toSubmodule S₄.toSubalgebra))) = 4 ∧
      sigNeg ((Algebra.traceForm ℚ L).toQuadraticMap.restrict
        ((Algebra.traceForm ℚ L).orthogonal (Subalgebra.toSubmodule S₄.toSubalgebra))) = 4 := by
  rw [orthogonal_S₄_eq_ker]
  exact transverse_S₄_type

/-- **Statement (13), bundled for the cubic sector**: `L = S₃ ⊕ S₃^⊥`, the restriction is
`4 · Tr_{S₃}` of type `(2, 1)`, the complement has type `(5, 4)`. -/
theorem orthogonal_decomposition_S₃ :
    IsCompl (Subalgebra.toSubmodule S₃.toSubalgebra)
        ((Algebra.traceForm ℚ L).orthogonal (Subalgebra.toSubmodule S₃.toSubalgebra)) ∧
      QuadraticMap.Equivalent
        ((Algebra.traceForm ℚ L).toQuadraticMap.restrict (Subalgebra.toSubmodule S₃.toSubalgebra))
        ((4 : ℚ) • (Algebra.traceForm ℚ S₃).toQuadraticMap) ∧
      (sigPos ((Algebra.traceForm ℚ L).toQuadraticMap.restrict
          (Subalgebra.toSubmodule S₃.toSubalgebra)) = 2 ∧
        sigNeg ((Algebra.traceForm ℚ L).toQuadraticMap.restrict
          (Subalgebra.toSubmodule S₃.toSubalgebra)) = 1) ∧
      (sigPos (transverseForm S₃) = 5 ∧ sigNeg (transverseForm S₃) = 4) :=
  ⟨isCompl_S₃_orthogonal, restrict_S₃_equivalent, restrict_S₃_type, transverse_S₃_type⟩

/-- **Statement (13), bundled for the quartic sector**: `L = S₄ ⊕ S₄^⊥`, the restriction is
`3 · Tr_{S₄}` of type `(3, 1)`, the complement has type `(4, 4)`. -/
theorem orthogonal_decomposition_S₄ :
    IsCompl (Subalgebra.toSubmodule S₄.toSubalgebra)
        ((Algebra.traceForm ℚ L).orthogonal (Subalgebra.toSubmodule S₄.toSubalgebra)) ∧
      QuadraticMap.Equivalent
        ((Algebra.traceForm ℚ L).toQuadraticMap.restrict (Subalgebra.toSubmodule S₄.toSubalgebra))
        ((3 : ℚ) • (Algebra.traceForm ℚ S₄).toQuadraticMap) ∧
      (sigPos ((Algebra.traceForm ℚ L).toQuadraticMap.restrict
          (Subalgebra.toSubmodule S₄.toSubalgebra)) = 3 ∧
        sigNeg ((Algebra.traceForm ℚ L).toQuadraticMap.restrict
          (Subalgebra.toSubmodule S₄.toSubalgebra)) = 1) ∧
      (sigPos (transverseForm S₄) = 4 ∧ sigNeg (transverseForm S₄) = 4) :=
  ⟨isCompl_S₄_orthogonal, restrict_S₄_equivalent, restrict_S₄_type, transverse_S₄_type⟩

/-! ### (14) The covolume of `𝓞 L` in the mixed space `ℝ² × ℂ⁵`

Mathlib's normalization throughout: the mixed space is
`({w // IsReal w} → ℝ) × ({w // IsComplex w} → ℂ)` with `MeasureTheory.volume` the product
Lebesgue measure (`ℂ` carrying the Lebesgue measure of `ℝ²`), and `covolume_integerLattice` reads
`covol(𝓞 K) = 2^{−r₂} · √|discr K|`. -/

open scoped Classical in
/-- `covol(𝓞 S₃) = 2⁻¹ · √23` (`r₂ = 1`, `discr = −23`). -/
theorem covolume_S₃ :
    ZLattice.covolume (mixedEmbedding.integerLattice S₃) = 2⁻¹ * Real.sqrt 23 := by
  rw [mixedEmbedding.covolume_integerLattice, nrComplexPlaces_S₃, discr_S₃, pow_one]
  have h : |((-23 : ℤ) : ℝ)| = 23 := by
    push_cast
    rw [abs_neg, abs_of_pos (by norm_num)]
  rw [h]

open scoped Classical in
/-- `covol(𝓞 S₄) = 2⁻¹ · √283` (`r₂ = 1`, `discr = −283`). -/
theorem covolume_S₄ :
    ZLattice.covolume (mixedEmbedding.integerLattice S₄) = 2⁻¹ * Real.sqrt 283 := by
  rw [mixedEmbedding.covolume_integerLattice, nrComplexPlaces_S₄, discr_S₄, pow_one]
  have h : |((-283 : ℤ) : ℝ)| = 283 := by
    push_cast
    rw [abs_neg, abs_of_pos (by norm_num)]
  rw [h]

open scoped Classical in
/-- **Statement (14)**: the covolume of `𝓞 L` in the mixed space `ℝ² × ℂ⁵` is
`2⁻⁵ · 23² · 283 · √283` (`≈ 78701.9`, the decimal is not part of the theorem): Mathlib's
`covolume_integerLattice` on `nrComplexPlaces_L = 5` and `discr_L = −23⁴ · 283³`. -/
theorem covolume_L :
    ZLattice.covolume (mixedEmbedding.integerLattice L) =
      2⁻¹ ^ 5 * (23 ^ 2 * 283 * Real.sqrt 283) := by
  rw [mixedEmbedding.covolume_integerLattice, nrComplexPlaces_L, discr_L]
  have h : |((-6342648595267 : ℤ) : ℝ)| = (23 ^ 2 * 283) ^ 2 * 283 := by
    push_cast
    rw [abs_neg, abs_of_pos (by norm_num)]
    norm_num
  rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

open scoped Classical in
/-- **The normalization, made explicit** (the rider to (14)): `covol(𝓞 L)` is `4` times
`covol(𝓞 S₃)⁴ · covol(𝓞 S₄)³`, not that product — the sectors have `r₂ = 1` each, so the product
carries `2^{−(4·1 + 3·1)} = 2⁻⁷` against `L`'s `2⁻⁵`. -/
theorem covolume_L_eq_four_mul :
    ZLattice.covolume (mixedEmbedding.integerLattice L) =
      4 * ZLattice.covolume (mixedEmbedding.integerLattice S₃) ^ 4 *
        ZLattice.covolume (mixedEmbedding.integerLattice S₄) ^ 3 := by
  rw [covolume_L, covolume_S₃, covolume_S₄]
  have h23 : Real.sqrt 23 ^ 2 = 23 := Real.sq_sqrt (by norm_num)
  have h283 : Real.sqrt 283 ^ 2 = 283 := Real.sq_sqrt (by norm_num)
  linear_combination (-4 * 2⁻¹ ^ 7 * Real.sqrt 283 ^ 3 * (Real.sqrt 23 ^ 2 + 23)) * h23 +
    (-(2⁻¹ ^ 5) * 23 ^ 2 * Real.sqrt 283) * h283

/-! ### Statement 15: the minimal polynomial of `ρQ` and the index `53` -/

/-- `ρQ` is a root of the ruler polynomial. The certificate is an explicit ideal membership
`rulerPoly(ρQ) = A · (ρ³ − ρ − 1) + B · (Q⁴ − Q − 1)` in `ℤ[ρ, Q]` (cofactors computed by
SymPy's Gröbner reduction, checked here by `ring`). -/
theorem aeval_ρQ_rulerPolyQ : aeval (ρ * Q) rulerPolyQ = 0 := by
  have hρ := ρ_cubic
  have hQ := Q_quartic
  simp only [rulerPolyQ, map_sub, map_add, map_mul, map_pow, aeval_X, map_ofNat, map_one]
  linear_combination
    (ρ ^ 9 * Q ^ 12 + ρ ^ 7 * Q ^ 12 + ρ ^ 6 * Q ^ 12 - 3 * ρ ^ 6 * Q ^ 9 + ρ ^ 5 * Q ^ 12
      - 2 * ρ ^ 5 * Q ^ 8 + 2 * ρ ^ 4 * Q ^ 12 - 3 * ρ ^ 4 * Q ^ 9 + 2 * ρ ^ 3 * Q ^ 12
      - 3 * ρ ^ 3 * Q ^ 9 - 2 * ρ ^ 3 * Q ^ 8 + 2 * ρ ^ 3 * Q ^ 6 + 3 * ρ ^ 2 * Q ^ 12
      - 3 * ρ ^ 2 * Q ^ 9 - 2 * ρ ^ 2 * Q ^ 8 - ρ ^ 2 * Q ^ 5 + 4 * ρ * Q ^ 12 - 6 * ρ * Q ^ 9
      - 2 * ρ * Q ^ 8 + 2 * ρ * Q ^ 6 - 3 * ρ * Q ^ 4 + 5 * Q ^ 12 - 6 * Q ^ 9 - 4 * Q ^ 8
      + 2 * Q ^ 6 - Q ^ 5 - Q ^ 3) * hρ +
    (7 * ρ ^ 2 * Q ^ 8 - 2 * ρ ^ 2 * Q ^ 5 + 3 * ρ ^ 2 * Q ^ 4 + 9 * ρ * Q ^ 8 - 3 * ρ * Q ^ 5
      + 3 * ρ * Q ^ 4 + ρ * Q ^ 2 - ρ * Q + 5 * Q ^ 8 - Q ^ 5 + Q ^ 4 + Q ^ 2 - Q + 1) * hQ

/-- `Q ∉ S₃`: otherwise `S₄ ≤ S₃` and `4 ∣ 3`. -/
theorem Q_not_mem_S₃ : Q ∉ S₃ := by
  intro h
  have hle : S₄ ≤ S₃ := adjoin_simple_le_iff.mpr h
  have hdvd := finrank_dvd_of_le_right hle
  rw [finrank_S₃, finrank_S₄] at hdvd
  omega

/-- `ρ ∉ S₄`: otherwise `S₃ ≤ S₄` and `3 ∣ 4`. -/
theorem ρ_not_mem_S₄ : ρ ∉ S₄ := by
  intro h
  have hle : S₃ ≤ S₄ := adjoin_simple_le_iff.mpr h
  have hdvd := finrank_dvd_of_le_right hle
  rw [finrank_S₃, finrank_S₄] at hdvd
  omega

/-- `ρQ ∉ S₃` (else `Q = ρ⁻¹ · ρQ ∈ S₃`). -/
theorem mul_not_mem_S₃ : ρ * Q ∉ S₃ := by
  intro h
  apply Q_not_mem_S₃
  have hρ : ρ ∈ S₃ := mem_adjoin_simple_self ℚ ρ
  have hQ : Q = ρ⁻¹ * (ρ * Q) := by rw [← mul_assoc, inv_mul_cancel₀ ρ_ne_zero, one_mul]
  rw [hQ]
  exact mul_mem (S₃.inv_mem hρ) h

/-- `ρQ ∉ S₄` (else `ρ = Q⁻¹ · ρQ ∈ S₄`). -/
theorem mul_not_mem_S₄ : ρ * Q ∉ S₄ := by
  intro h
  apply ρ_not_mem_S₄
  have hQ : Q ∈ S₄ := mem_adjoin_simple_self ℚ Q
  have hρ : ρ = Q⁻¹ * (ρ * Q) := by
    rw [mul_comm ρ Q, ← mul_assoc, inv_mul_cancel₀ Q_ne_zero, one_mul]
  rw [hρ]
  exact mul_mem (S₄.inv_mem hQ) h

/-- `ℚ⟮ρQ⟯ = L`: by the subfield lattice of `Extras`, `ℚ⟮ρQ⟯ ∈ {ℚ, S₃, S₄, L}`, and `ρQ` lies in
neither sector (nor in `ℚ ≤ S₃`). -/
theorem adjoin_ρQ_eq_top : ℚ⟮ρ * Q⟯ = ⊤ := by
  have hmem : ρ * Q ∈ ℚ⟮ρ * Q⟯ := mem_adjoin_simple_self ℚ (ρ * Q)
  rcases subfield_lattice finrank_L ρ Q ρ_cubic Q_quartic ℚ⟮ρ * Q⟯ with h | h | h | h
  · have h' : ρ * Q ∈ (⊥ : IntermediateField ℚ L) := h ▸ hmem
    exact absurd (bot_le (a := S₃) h') mul_not_mem_S₃
  · have h' : ρ * Q ∈ ℚ⟮ρ⟯ := h ▸ hmem
    exact absurd h' mul_not_mem_S₃
  · have h' : ρ * Q ∈ ℚ⟮Q⟯ := h ▸ hmem
    exact absurd h' mul_not_mem_S₄
  · exact h

theorem rulerPolyQ_monic : rulerPolyQ.Monic := by
  rw [← rulerPoly_map_rat]; exact rulerPoly_monic.map _

theorem rulerPolyQ_natDegree : rulerPolyQ.natDegree = 12 := by
  rw [← rulerPoly_map_rat, rulerPoly_monic.natDegree_map, rulerPoly_natDegree]

/-- **The minimal polynomial of `ρQ` over `ℚ` is the ruler polynomial**
`X¹² − 3X⁹ − 2X⁸ + 2X⁶ − X⁵ − 3X⁴ − X³ + X − 1`: `ρQ` is a root, and `ℚ⟮ρQ⟯ = L` has degree
`12`. (The hypothesis `hmin` of `Extras`, discharged.) -/
theorem minpoly_ρQ : minpoly ℚ (ρ * Q) = rulerPolyQ := by
  have hint : IsIntegral ℚ (ρ * Q) := ρ_isIntegral.mul Q_isIntegral
  have hdvd : minpoly ℚ (ρ * Q) ∣ rulerPolyQ := minpoly.dvd ℚ _ aeval_ρQ_rulerPolyQ
  have hmindeg : (minpoly ℚ (ρ * Q)).natDegree = 12 := by
    rw [← adjoin.finrank hint, adjoin_ρQ_eq_top, finrank_top', finrank_L]
  symm
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) rulerPolyQ_monic hdvd
    (by rw [rulerPolyQ_natDegree, hmindeg])

/-- `ρQ` as an element of `𝓞 L`. -/
noncomputable abbrev ρQ' : 𝓞 L := ρ' * Q'

theorem coe_ρQ' : algebraMap (𝓞 L) L ρQ' = ρ * Q := by
  rw [ρQ', map_mul, coe_ρ', coe_Q']

/-- **The index on the concrete field**: `[𝓞 L : ℤ[ρQ]] = 53` — `index_eq_53_of_minpoly` (`Extras`)
with all three hypotheses discharged (`finrank_L`, `minpoly_ρQ`, `discr_L`). -/
theorem index_ρQ_eq_53 :
    (Submodule.span ℤ (Set.range (fun i : Fin 12 => ρQ' ^ (i : ℕ)))).toAddSubgroup.index = 53 :=
  index_eq_53_of_minpoly ρQ' finrank_L (by rw [coe_ρQ']; exact minpoly_ρQ) discr_L

/-! ### Statements 16–18 on the concrete field -/

/-- **The subfield lattice of `L`** is `{ℚ, S₃, S₄, L}` (`subfield_lattice` of `Extras` instantiated). -/
theorem subfield_lattice_L (F : IntermediateField ℚ L) : F = ⊥ ∨ F = S₃ ∨ F = S₄ ∨ F = ⊤ :=
  subfield_lattice finrank_L ρ Q ρ_cubic Q_quartic F

/-- **Root-rigidity of `L`**: no irreducible polynomial over `ℚ` has two distinct roots in `L`
(`rootRigid_of_roots` of `Extras` instantiated). -/
theorem rootRigid_L : RootRigid L := rootRigid_of_roots finrank_L ρ Q ρ_cubic Q_quartic

/-- **`L` is circle-free**: the only elements with a complex embedding of modulus `1` are `±1`
(`circle_free` of `Extras` instantiated). -/
theorem circle_free_L (α : L) (σ : L →+* ℂ) (hα : ‖σ α‖ = 1) : α = 1 ∨ α = -1 :=
  circle_free finrank_L ρ Q ρ_cubic Q_quartic α σ hα

/-- **Smyth's floor on `𝓞 L`** (`Extras` instantiated; Smyth's theorem is the hypothesis `smyth`,
cited not proved): every `α ∈ 𝓞 L` with `α ≠ 0, ±1` has Mahler measure `≥ θ`. -/
theorem mahlerMeasure_ge_of_smyth_L (θ : ℝ)
    (smyth : ∀ p : ℤ[X], p.Monic → p.coeff 0 ≠ 0 → p.reverse ≠ p → p.reverse ≠ -p →
      θ ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure)
    (α : 𝓞 L) (hα0 : α ≠ 0) (h1 : α ≠ 1) (h2 : α ≠ -1) :
    θ ≤ ((minpoly ℤ (algebraMap (𝓞 L) L α)).map (Int.castRingHom ℂ)).mahlerMeasure :=
  mahlerMeasure_ge_of_smyth_ringOfIntegers rootRigid_L θ smyth α hα0 h1 h2

end HermiteCompositum.Assembly
