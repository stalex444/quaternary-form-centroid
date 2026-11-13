module
public import Mathlib
public import HermiteCompositum.Defs

@[expose] public section

/-!
# Trace projection and transverse type (compared statement 5)

For a finite extension `E / K` of fields and an intermediate field `F`, with `Tr_{E/K}(xy)` the
trace form of `E / K`:

* **(5a) tower identity and projection.** `Tr_{E/K}(x·a) = Tr_{F/K}(Tr_{E/F}(x)·a)` for `x ∈ E`,
  `a ∈ F` (`trace_mul_algebraMap`). Hence `π := [E:F]⁻¹·Tr_{E/F}` is an `F`-linear endomorphism
  of `E` (`traceProj`) with values in `F` (`traceProj_mem`), fixing `F` (`traceProj_algebraMap`),
  idempotent (`traceProj_traceProj`), and with kernel `ker Tr_{E/F}` (`traceProj_eq_zero_iff`).
  That kernel is the orthogonal complement `F^⊥` of `F` for the trace form
  (`orthogonal_eq_ker_trace`, separable case), and `E = F ⊕ F^⊥` as `K`-spaces
  (`isCompl_ker_trace`, `isCompl_orthogonal`).
* **(5b) on `F`.** `Tr_{E/K}(ab) = [E:F]·Tr_{F/K}(ab)` (`trace_algebraMap_mul`); as quadratic
  forms, `Tr_{E/K}(x²)` restricted to `F` is isometric to `[E:F]·Tr_{F/K}(x²)`
  (`restrictTraceFormIsometryEquiv`).
* **(5c) transverse type.** For a number field `E` and `F : IntermediateField ℚ E`, the
  restriction of `Tr_{E/ℚ}(x²)` to `ker Tr_{E/F}` (`transverseForm`) has
  `sigPos = r₁(E) + r₂(E) − r₁(F) − r₂(F)` and `sigNeg = r₂(E) − r₂(F)`
  (`transverseForm_signature`; additive forms `sigPos_transverseForm_add`,
  `sigNeg_transverseForm_add`). **Hypotheses:** the trace-form signatures of `E` and of `F`
  (compared statement 2: `sigPos = r₁ + r₂`, `sigNeg = r₂`) are taken as explicit hypotheses
  `hE₁ hE₂ hF₁ hF₂`, so this file does not depend on `TraceSignature`; `Assembly` discharges them.

Supporting general lemmas on signatures (not in Mathlib at this pin): `sigPos`/`sigNeg` are
additive over a product (`sigPos_prod`, `sigNeg_prod`) and over an orthogonal direct-sum
decomposition `M = W ⊕ W'` of any quadratic form (`sigPos_restrict_add_sigPos_restrict`,
`sigNeg_restrict_add_sigNeg_restrict`; no nondegeneracy needed), and invariant under a positive
scalar (`sigPos_smul_of_pos`, `sigNeg_smul_of_pos`). The proofs reduce to weighted sums of squares
via Mathlib's `equivalent_weightedSumSquares` and the uniqueness half of Sylvester's law
(`sigPos_of_equiv_weightedSumSquares`).

Throughout, `F` as a `K`-subspace of `E` is written `Subalgebra.toSubmodule F.toSubalgebra`.
-/

open Module QuadraticForm QuadraticMap

namespace HermiteCompositum

/-! ### (5a), (5b): the tower identity, the trace projection, and the orthogonal complement -/

section Tower

variable {K E : Type*} [Field K] [Field E] [Algebra K E] (F : IntermediateField K E)
  [FiniteDimensional K E]

/-- **(5a) tower identity**: `Tr_{E/K}(x·a) = Tr_{F/K}(Tr_{E/F}(x)·a)` for `x ∈ E`, `a ∈ F`.
(`Algebra.trace_trace` and the `F`-linearity of `Tr_{E/F}`.) -/
theorem trace_mul_algebraMap (x : E) (a : F) :
    Algebra.trace K E (x * algebraMap F E a) = Algebra.trace K F (Algebra.trace F E x * a) := by
  have : FiniteDimensional F E := Module.Finite.right K F E
  rw [← Algebra.trace_trace (S := F), mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul,
    mul_comm]

/-- **(5b) on `F`**: `Tr_{E/K}(ab) = [E:F]·Tr_{F/K}(ab)` for `a, b ∈ F`. -/
theorem trace_algebraMap_mul (a b : F) :
    Algebra.trace K E (algebraMap F E a * algebraMap F E b) =
      finrank F E • Algebra.trace K F (a * b) := by
  have : FiniteDimensional F E := Module.Finite.right K F E
  rw [← map_mul, ← Algebra.trace_trace (S := F), Algebra.trace_algebraMap, map_nsmul]

-- `traceProj` is defined in `HermiteCompositum/Defs.lean` (shared verbatim with `Challenge.lean`).

omit [FiniteDimensional K E] in
theorem traceProj_apply (x : E) :
    traceProj F x = algebraMap F E ((finrank F E : F)⁻¹ * Algebra.trace F E x) := by
  simp [traceProj, Algebra.smul_def, map_mul]

omit [FiniteDimensional K E] in
/-- `π` takes values in `F`. -/
theorem traceProj_mem (x : E) : traceProj F x ∈ F := by
  rw [traceProj_apply, IntermediateField.algebraMap_apply]; exact Subtype.mem _

/-- `π` fixes `F` pointwise (so `π` is onto `F`). Needs `[E:F] ≠ 0` in `K`, i.e. `CharZero K`. -/
theorem traceProj_algebraMap [CharZero K] (a : F) :
    traceProj F (algebraMap F E a) = algebraMap F E a := by
  have : FiniteDimensional F E := Module.Finite.right K F E
  rw [traceProj_apply, Algebra.trace_algebraMap, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀, one_mul]
  exact_mod_cast (Module.finrank_pos (R := F) (M := E)).ne'

/-- `π` is idempotent. -/
theorem traceProj_traceProj [CharZero K] (x : E) :
    traceProj F (traceProj F x) = traceProj F x := by
  rw [traceProj_apply F x, traceProj_algebraMap]

/-- `ker π = ker Tr_{E/F}`. -/
theorem traceProj_eq_zero_iff [CharZero K] (x : E) :
    traceProj F x = 0 ↔ Algebra.trace F E x = 0 := by
  have : FiniteDimensional F E := Module.Finite.right K F E
  rw [traceProj_apply, map_eq_zero_iff _ (algebraMap F E).injective, mul_eq_zero, inv_eq_zero]
  have h : (finrank F E : F) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := F) (M := E)).ne'
  simp [h]

/-- `x − π x ∈ ker Tr_{E/F}`: the explicit decomposition `x = π x + (x − π x)`. -/
theorem trace_sub_traceProj [CharZero K] (x : E) :
    Algebra.trace F E (x - traceProj F x) = 0 := by
  have : FiniteDimensional F E := Module.Finite.right K F E
  rw [map_sub, traceProj_apply, Algebra.trace_algebraMap, nsmul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀, one_mul, sub_self]
  exact_mod_cast (Module.finrank_pos (R := F) (M := E)).ne'

/-- **`ker Tr_{E/F} = F^⊥`**: the kernel of `Tr_{E/F}` is the orthogonal complement of `F` for
the trace form of `E/K` (separable case; automatic in characteristic zero). -/
theorem orthogonal_eq_ker_trace [Algebra.IsSeparable K E] :
    (Algebra.traceForm K E).orthogonal (Subalgebra.toSubmodule F.toSubalgebra) =
      LinearMap.ker ((Algebra.trace F E).restrictScalars K) := by
  ext x
  rw [LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.mem_ker, LinearMap.restrictScalars_apply]
  constructor
  · intro h
    refine (traceForm_nondegenerate K F).1 (Algebra.trace F E x) fun a => ?_
    rw [Algebra.traceForm_apply, ← trace_mul_algebraMap, mul_comm, ← Algebra.traceForm_apply]
    exact h _ a.2
  · intro h n hn
    have key := trace_mul_algebraMap F x ⟨n, hn⟩
    rw [h, zero_mul, map_zero] at key
    rw [Algebra.traceForm_apply, mul_comm]
    exact key

/-- **`E = F ⊕ ker Tr_{E/F}`** as `K`-vector spaces. -/
theorem isCompl_ker_trace [CharZero K] :
    IsCompl (Subalgebra.toSubmodule F.toSubalgebra)
      (LinearMap.ker ((Algebra.trace F E).restrictScalars K)) := by
  let π : E →ₗ[K] Subalgebra.toSubmodule F.toSubalgebra :=
    ((traceProj F).restrictScalars K).codRestrict _ (traceProj_mem F)
  have hπ : ∀ y : Subalgebra.toSubmodule F.toSubalgebra, π y = y := fun y =>
    Subtype.ext (traceProj_algebraMap F ⟨y.1, y.2⟩)
  convert LinearMap.isCompl_of_proj hπ using 1
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.restrictScalars_apply,
    ← traceProj_eq_zero_iff]
  constructor
  · intro h; exact Subtype.ext h
  · intro h; exact congrArg Subtype.val h

/-- **`E = F ⊕ F^⊥`** for the trace form of `E/K`. -/
theorem isCompl_orthogonal [CharZero K] [Algebra.IsSeparable K E] :
    IsCompl (Subalgebra.toSubmodule F.toSubalgebra)
      ((Algebra.traceForm K E).orthogonal (Subalgebra.toSubmodule F.toSubalgebra)) := by
  rw [orthogonal_eq_ker_trace]; exact isCompl_ker_trace F

/-- `Tr_{E/K}(a·y) = 0` for `a ∈ F` and `y ∈ ker Tr_{E/F}`. -/
theorem traceForm_eq_zero_of_mem_ker_trace (a : E) (ha : a ∈ F)
    (y : E) (hy : Algebra.trace F E y = 0) :
    Algebra.traceForm K E a y = 0 := by
  have key := trace_mul_algebraMap F y ⟨a, ha⟩
  rw [hy, zero_mul, map_zero] at key
  rw [Algebra.traceForm_apply, mul_comm]
  exact key

/-- Elements of `F` and of `ker Tr_{E/F}` are orthogonal for the quadratic form `Tr_{E/K}(x²)`. -/
theorem isOrtho_of_mem_ker_trace (a : E) (ha : a ∈ Subalgebra.toSubmodule F.toSubalgebra)
    (y : E) (hy : y ∈ LinearMap.ker ((Algebra.trace F E).restrictScalars K)) :
    (Algebra.traceForm K E).toQuadraticMap.IsOrtho a y := by
  rw [LinearMap.mem_ker, LinearMap.restrictScalars_apply] at hy
  have h1 := traceForm_eq_zero_of_mem_ker_trace F a ha y hy
  have h2 : Algebra.traceForm K E y a = 0 := by
    rw [Algebra.traceForm_apply, mul_comm, ← Algebra.traceForm_apply]; exact h1
  rw [isOrtho_def, LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.BilinMap.toQuadraticMap_apply,
    LinearMap.BilinMap.toQuadraticMap_apply]
  simp only [map_add, LinearMap.add_apply, h1, h2]
  abel

end Tower

/-! ### Signatures over an orthogonal direct sum (supporting general lemmas) -/

section Counting

/-- Counting a predicate over a sum type. -/
theorem ncard_setOf_sum {α β : Type*} [Fintype α] [Fintype β] (p : α ⊕ β → Prop)
    [DecidablePred p] :
    {x | p x}.ncard = {a | p (Sum.inl a)}.ncard + {b | p (Sum.inr b)}.ncard := by
  classical
  have h1 : {x | p x} = ↑(Finset.univ.filter p) := by ext; simp
  have h2 : {a | p (Sum.inl a)} = ↑(Finset.univ.filter (fun a => p (Sum.inl a))) := by ext; simp
  have h3 : {b | p (Sum.inr b)} = ↑(Finset.univ.filter (fun b => p (Sum.inr b))) := by ext; simp
  rw [h1, h2, h3, Set.ncard_coe_finset, Set.ncard_coe_finset, Set.ncard_coe_finset,
    Finset.card_filter, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]

end Counting

section OrthogonalSum

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- `Q` is isometric to `Q|_W ⊕ Q|_W'` for complementary `Q`-orthogonal subspaces `W, W'`. -/
noncomputable def isometryEquivProdRestrict (Q : QuadraticForm R M) {W W' : Submodule R M}
    (h : IsCompl W W') (horth : ∀ x ∈ W, ∀ y ∈ W', Q.IsOrtho x y) :
    ((Q.restrict W).prod (Q.restrict W')).IsometryEquiv Q where
  toLinearEquiv := Submodule.prodEquivOfIsCompl W W' h
  map_app' x := by
    change Q (Submodule.prodEquivOfIsCompl W W' h x) = _
    rw [Submodule.coe_prodEquivOfIsCompl', QuadraticMap.prod_apply, QuadraticMap.restrict_apply,
      QuadraticMap.restrict_apply]
    exact horth x.1 x.1.2 x.2 x.2.2

end OrthogonalSum

section Signature

variable {𝕜 M M₁ M₂ : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup M] [Module 𝕜 M] [AddCommGroup M₁] [Module 𝕜 M₁] [AddCommGroup M₂] [Module 𝕜 M₂]

/-- A weighted sum of squares over a sum type is the product of the two weighted sums. -/
noncomputable def weightedSumSquaresSumIsometryEquiv {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (w₁ : ι₁ → 𝕜) (w₂ : ι₂ → 𝕜) :
    (weightedSumSquares 𝕜 (Sum.elim w₁ w₂)).IsometryEquiv
      ((weightedSumSquares 𝕜 w₁).prod (weightedSumSquares 𝕜 w₂)) where
  toLinearEquiv := LinearEquiv.sumArrowLequivProdArrow ι₁ ι₂ 𝕜 𝕜
  map_app' f := by
    simp [weightedSumSquares_apply, Fintype.sum_sum_type]

/-- **Additivity of `sigPos` over a product** of quadratic forms. -/
theorem sigPos_prod [FiniteDimensional 𝕜 M₁] [FiniteDimensional 𝕜 M₂]
    (Q₁ : QuadraticForm 𝕜 M₁) (Q₂ : QuadraticForm 𝕜 M₂) :
    sigPos (Q₁.prod Q₂) = sigPos Q₁ + sigPos Q₂ := by
  have : Invertible (2 : 𝕜) := invertibleOfNonzero (NeZero.ne _)
  obtain ⟨w₁, e₁⟩ := Q₁.equivalent_weightedSumSquares
  obtain ⟨w₂, e₂⟩ := Q₂.equivalent_weightedSumSquares
  have e : (Q₁.prod Q₂).Equivalent (weightedSumSquares 𝕜 (Sum.elim w₁ w₂)) :=
    (e₁.prod e₂).trans ⟨(weightedSumSquaresSumIsometryEquiv w₁ w₂).symm⟩
  rw [sigPos_of_equiv_weightedSumSquares e, sigPos_of_equiv_weightedSumSquares e₁,
    sigPos_of_equiv_weightedSumSquares e₂, ncard_setOf_sum]
  simp

/-- **Additivity of `sigNeg` over a product** of quadratic forms. -/
theorem sigNeg_prod [FiniteDimensional 𝕜 M₁] [FiniteDimensional 𝕜 M₂]
    (Q₁ : QuadraticForm 𝕜 M₁) (Q₂ : QuadraticForm 𝕜 M₂) :
    sigNeg (Q₁.prod Q₂) = sigNeg Q₁ + sigNeg Q₂ := by
  have : Invertible (2 : 𝕜) := invertibleOfNonzero (NeZero.ne _)
  obtain ⟨w₁, e₁⟩ := Q₁.equivalent_weightedSumSquares
  obtain ⟨w₂, e₂⟩ := Q₂.equivalent_weightedSumSquares
  have e : (Q₁.prod Q₂).Equivalent (weightedSumSquares 𝕜 (Sum.elim w₁ w₂)) :=
    (e₁.prod e₂).trans ⟨(weightedSumSquaresSumIsometryEquiv w₁ w₂).symm⟩
  rw [sigNeg_of_equiv_weightedSumSquares e, sigNeg_of_equiv_weightedSumSquares e₁,
    sigNeg_of_equiv_weightedSumSquares e₂, ncard_setOf_sum]
  simp

/-- **Additivity of `sigPos` over an orthogonal direct-sum decomposition** `M = W ⊕ W'`.
No nondegeneracy is assumed. -/
theorem sigPos_restrict_add_sigPos_restrict [FiniteDimensional 𝕜 M] (Q : QuadraticForm 𝕜 M)
    {W W' : Submodule 𝕜 M} (h : IsCompl W W') (horth : ∀ x ∈ W, ∀ y ∈ W', Q.IsOrtho x y) :
    sigPos (Q.restrict W) + sigPos (Q.restrict W') = sigPos Q := by
  rw [← sigPos_prod]
  exact QuadraticMap.Equivalent.sigPos_eq ⟨isometryEquivProdRestrict Q h horth⟩

/-- **Additivity of `sigNeg` over an orthogonal direct-sum decomposition** `M = W ⊕ W'`. -/
theorem sigNeg_restrict_add_sigNeg_restrict [FiniteDimensional 𝕜 M] (Q : QuadraticForm 𝕜 M)
    {W W' : Submodule 𝕜 M} (h : IsCompl W W') (horth : ∀ x ∈ W, ∀ y ∈ W', Q.IsOrtho x y) :
    sigNeg (Q.restrict W) + sigNeg (Q.restrict W') = sigNeg Q := by
  rw [← sigNeg_prod]
  exact QuadraticMap.Equivalent.sigNeg_eq ⟨isometryEquivProdRestrict Q h horth⟩

/-- `sigPos` is invariant under a positive scalar. -/
theorem sigPos_smul_of_pos [FiniteDimensional 𝕜 M] (Q : QuadraticForm 𝕜 M) {c : 𝕜} (hc : 0 < c) :
    sigPos (c • Q) = sigPos Q := by
  refine (sigPos_isGreatest (c • Q)).unique ?_
  convert sigPos_isGreatest Q using 1
  ext r
  simp only [Set.mem_ofPred_eq]
  refine exists_congr fun V => and_congr_right fun _ => ?_
  constructor
  · intro hV x hx
    have := hV x hx
    rw [restrict_apply, smul_apply] at this
    exact (smul_pos_iff_of_pos_left hc).mp this
  · intro hV x hx
    rw [restrict_apply, smul_apply]
    exact smul_pos hc (hV x hx)

/-- `sigNeg` is invariant under a positive scalar. -/
theorem sigNeg_smul_of_pos [FiniteDimensional 𝕜 M] (Q : QuadraticForm 𝕜 M) {c : 𝕜} (hc : 0 < c) :
    sigNeg (c • Q) = sigNeg Q := by
  have hneg : -(c • Q) = c • (-Q) := QuadraticMap.ext fun x => by simp
  rw [← sigPos_neg, hneg, sigPos_smul_of_pos _ hc, sigPos_neg]

end Signature

/-! ### (5b) as forms: the restriction of the trace form to `F` -/

section Transverse

variable {K E : Type*} [Field K] [Field E] [Algebra K E] (F : IntermediateField K E)
  [FiniteDimensional K E]

/-- `F` as a `K`-subspace of `E`, identified with the field `F`. -/
noncomputable def subfieldEquiv : Subalgebra.toSubmodule F.toSubalgebra ≃ₗ[K] F where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [FiniteDimensional K E] in
@[simp] theorem subfieldEquiv_apply_coe (x : Subalgebra.toSubmodule F.toSubalgebra) :
    ((subfieldEquiv F x : F) : E) = x := rfl

/-- **(5b) as forms**: the trace form of `E/K` restricted to `F` is isometric to `[E:F]` times
the trace form of `F/K`. -/
noncomputable def restrictTraceFormIsometryEquiv :
    ((Algebra.traceForm K E).toQuadraticMap.restrict
      (Subalgebra.toSubmodule F.toSubalgebra)).IsometryEquiv
      ((finrank F E : K) • (Algebra.traceForm K F).toQuadraticMap) where
  toLinearEquiv := subfieldEquiv F
  map_app' x := by
    change ((finrank F E : K) • (Algebra.traceForm K F).toQuadraticMap) (subfieldEquiv F x) = _
    rw [smul_apply, restrict_apply, LinearMap.BilinMap.toQuadraticMap_apply,
      LinearMap.BilinMap.toQuadraticMap_apply, Algebra.traceForm_apply, Algebra.traceForm_apply,
      smul_eq_mul, ← nsmul_eq_mul]
    exact (trace_algebraMap_mul F (subfieldEquiv F x) (subfieldEquiv F x)).symm

end Transverse

/-! ### (5c): the transverse type over `ℚ` -/

section NumberField

open NumberField NumberField.InfinitePlace

variable {E : Type*} [Field E] [NumberField E] (F : IntermediateField ℚ E)

/-- Over `ℚ`, `ker Tr_{E/F} = F^⊥` with no side conditions (separability is automatic). -/
theorem orthogonal_eq_ker_trace_rat :
    (Algebra.traceForm ℚ E).orthogonal (Subalgebra.toSubmodule F.toSubalgebra) =
      LinearMap.ker ((Algebra.trace F E).restrictScalars ℚ) :=
  orthogonal_eq_ker_trace F

/-- Over `ℚ`, `E = F ⊕ F^⊥` with no side conditions. -/
theorem isCompl_orthogonal_rat :
    IsCompl (Subalgebra.toSubmodule F.toSubalgebra)
      ((Algebra.traceForm ℚ E).orthogonal (Subalgebra.toSubmodule F.toSubalgebra)) :=
  isCompl_orthogonal F

-- `transverseForm` is defined in `HermiteCompositum/Defs.lean` (shared verbatim with
-- `Challenge.lean`).

/-- The restriction of `Tr_{E/ℚ}(x²)` to `F` has the `sigPos` of the trace form of `F`. -/
theorem sigPos_restrict_subfield :
    sigPos ((Algebra.traceForm ℚ E).toQuadraticMap.restrict (Subalgebra.toSubmodule F.toSubalgebra))
      = sigPos (Algebra.traceForm ℚ F).toQuadraticMap := by
  rw [QuadraticMap.Equivalent.sigPos_eq ⟨restrictTraceFormIsometryEquiv F⟩, sigPos_smul_of_pos]
  exact_mod_cast Module.finrank_pos

/-- The restriction of `Tr_{E/ℚ}(x²)` to `F` has the `sigNeg` of the trace form of `F`. -/
theorem sigNeg_restrict_subfield :
    sigNeg ((Algebra.traceForm ℚ E).toQuadraticMap.restrict (Subalgebra.toSubmodule F.toSubalgebra))
      = sigNeg (Algebra.traceForm ℚ F).toQuadraticMap := by
  rw [QuadraticMap.Equivalent.sigNeg_eq ⟨restrictTraceFormIsometryEquiv F⟩, sigNeg_smul_of_pos]
  exact_mod_cast Module.finrank_pos

/-- **(5c), positive index, additive form**: `sigPos (transverse) + (r₁(F) + r₂(F)) = r₁(E) + r₂(E)`.
Hypotheses `hE`, `hF`: the trace-form signatures of `E` and `F` (compared statement 2, `TraceSignature`),
discharged in `Assembly`. -/
theorem sigPos_transverseForm_add
    (hE : sigPos (Algebra.traceForm ℚ E).toQuadraticMap = nrRealPlaces E + nrComplexPlaces E)
    (hF : sigPos (Algebra.traceForm ℚ F).toQuadraticMap = nrRealPlaces F + nrComplexPlaces F) :
    sigPos (transverseForm F) + (nrRealPlaces F + nrComplexPlaces F) =
      nrRealPlaces E + nrComplexPlaces E := by
  rw [← hE, ← hF, ← sigPos_restrict_subfield, add_comm]
  exact sigPos_restrict_add_sigPos_restrict _ (isCompl_ker_trace F) (isOrtho_of_mem_ker_trace F)

/-- **(5c), negative index, additive form**: `sigNeg (transverse) + r₂(F) = r₂(E)`.
Hypotheses `hE`, `hF` as in `sigPos_transverseForm_add`. -/
theorem sigNeg_transverseForm_add
    (hE : sigNeg (Algebra.traceForm ℚ E).toQuadraticMap = nrComplexPlaces E)
    (hF : sigNeg (Algebra.traceForm ℚ F).toQuadraticMap = nrComplexPlaces F) :
    sigNeg (transverseForm F) + nrComplexPlaces F = nrComplexPlaces E := by
  rw [← hE, ← hF, ← sigNeg_restrict_subfield, add_comm]
  exact sigNeg_restrict_add_sigNeg_restrict _ (isCompl_ker_trace F) (isOrtho_of_mem_ker_trace F)

/-- **(5c) transverse type**: the restriction of `Tr_{E/ℚ}(x²)` to `ker Tr_{E/F}` has
`sigPos = r₁(E) + r₂(E) − r₁(F) − r₂(F)` and `sigNeg = r₂(E) − r₂(F)` (natural-number
subtraction; the additive forms above show nothing is truncated).
Hypotheses `hE₁ hE₂ hF₁ hF₂`: the trace-form signatures of `E` and of `F` (compared statement 2,
`TraceSignature`), discharged in `Assembly`. -/
theorem transverseForm_signature
    (hE₁ : sigPos (Algebra.traceForm ℚ E).toQuadraticMap = nrRealPlaces E + nrComplexPlaces E)
    (hE₂ : sigNeg (Algebra.traceForm ℚ E).toQuadraticMap = nrComplexPlaces E)
    (hF₁ : sigPos (Algebra.traceForm ℚ F).toQuadraticMap = nrRealPlaces F + nrComplexPlaces F)
    (hF₂ : sigNeg (Algebra.traceForm ℚ F).toQuadraticMap = nrComplexPlaces F) :
    sigPos (transverseForm F) =
        nrRealPlaces E + nrComplexPlaces E - nrRealPlaces F - nrComplexPlaces F ∧
      sigNeg (transverseForm F) = nrComplexPlaces E - nrComplexPlaces F := by
  have h1 := sigPos_transverseForm_add F hE₁ hF₁
  have h2 := sigNeg_transverseForm_add F hE₂ hF₂
  omega

end NumberField

end HermiteCompositum
