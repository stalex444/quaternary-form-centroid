module
public import Mathlib
public import HermiteCompositum.Hermite

@[expose] public section

/-!
# The trace-form signature of a number field (Hermite–Sylvester; in number-field form, O. Taussky 1968)

For a number field `K`, the trace form `(x, y) ↦ Tr_{K/ℚ}(xy)` is a rational quadratic form on
`K`. Its signature is the place type of `K`:

* `sigPos (Algebra.traceForm ℚ K).toQuadraticMap = nrRealPlaces K + nrComplexPlaces K`,
* `sigNeg (Algebra.traceForm ℚ K).toQuadraticMap = nrComplexPlaces K`,

and consequently the trace form is positive definite iff `K` is totally real.

**Route.** Fix a power basis `1, θ, …, θ^{n−1}` of `K/ℚ` (`PowerBasis ℚ K`; a primitive element
exists by `Field.powerBasisOfFiniteOfSeparable`). In this basis the Gram matrix of the trace form
is `(Tr(θ^{i+j}))_{i,j}`, and `Tr(θ^k) = ∑_σ σ(θ)^k` over the complex embeddings
(`trace_eq_sum_embeddings`), which is the `k`-th power sum of the complex roots of the minimal
polynomial `g = minpoly ℚ θ` (`PowerBasis.liftEquiv'`; the roots are simple since `g` is
separable). So the Gram matrix is the Hermite matrix of `g` read over `ℝ`, and Hermite's
signature theorem (`HermiteCompositum.sigPos_hermiteForm`, `sigNeg_hermiteForm`) counts
`#R + #C⁺` and `#C⁺`. Finally the complex embeddings correspond to the roots, real embeddings
to real roots, and the non-real embeddings come in `2 · nrComplexPlaces K` conjugate pairs
(`card_real_embeddings`, `card_complex_embeddings`).

The one piece of plumbing is that the signature of a quadratic form given by a **rational**
matrix is the same whether the form is read over `ℚ` or over `ℝ`
(`sigPos_toQuadraticForm'_map`, `sigNeg_toQuadraticForm'_map`): a rational diagonalisation
`M ∼ diag(w)` is a matrix identity `M + Mᵀ = 2 Pᵀ diag(w) P` with `P` invertible over `ℚ`, which
survives the base change, and Sylvester's law of inertia
(`QuadraticForm.sigPos_of_equiv_weightedSumSquares`) counts the same weights on both sides.
-/

namespace HermiteCompositum

open Polynomial Finset Matrix NumberField NumberField.InfinitePlace
open scoped ComplexConjugate

noncomputable section

/-! ### T1: the signature of a rational matrix form is invariant under `ℚ → ℝ` -/

section MatrixForms

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- `M.toQuadraticForm' c = ∑ i, ∑ j, c i * M i j * c j`. -/
theorem toQuadraticForm'_apply (M : Matrix n n R) (c : n → R) :
    M.toQuadraticForm' c = ∑ i, ∑ j, c i * M i j * c j := by
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply, smul_eq_mul]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

theorem toQuadraticForm'_add (M N : Matrix n n R) (c : n → R) :
    (M + N).toQuadraticForm' c = M.toQuadraticForm' c + N.toQuadraticForm' c := by
  simp only [toQuadraticForm'_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

theorem toQuadraticForm'_transpose (M : Matrix n n R) (c : n → R) :
    Mᵀ.toQuadraticForm' c = M.toQuadraticForm' c := by
  simp only [toQuadraticForm'_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

/-- Polarisation of the matrix form at two basis vectors recovers `M i j + M j i`. -/
theorem polar_toQuadraticForm'_single (M : Matrix n n R) (i j : n) :
    QuadraticMap.polar (M.toQuadraticForm') (Pi.single i 1) (Pi.single j 1) = M i j + M j i := by
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.polar_toQuadraticMap,
    Matrix.toLinearMap₂'_apply, Pi.single_apply, smul_eq_mul]
  simp [Finset.sum_ite_eq']

/-- Two matrix forms that agree as functions have the same symmetrisation. -/
theorem add_transpose_eq_of_toQuadraticForm'_eq {M N : Matrix n n R}
    (h : ∀ c, M.toQuadraticForm' c = N.toQuadraticForm' c) : M + Mᵀ = N + Nᵀ := by
  ext i j
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.transpose_apply,
    ← polar_toQuadraticForm'_single, ← polar_toQuadraticForm'_single]
  simp only [QuadraticMap.polar, h]

omit [Fintype n] [DecidableEq n] in
theorem transpose_mul_diagonal_mul_apply {m : Type*} [Fintype m] [DecidableEq m]
    (w : m → R) (P : Matrix m n R) (j k : n) :
    (Pᵀ * diagonal w * P) j k = ∑ i, P i j * w i * P i k := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

omit [DecidableEq n] in
theorem mulVec_apply_sum {m : Type*} (P : Matrix m n R) (c : n → R) (i : m) :
    (P *ᵥ c) i = ∑ j, P i j * c j := rfl

/-- A weighted sum of squares pulled back along a matrix `P` is the form of `Pᵀ diag(w) P`. -/
theorem weightedSumSquares_mulVec {m : Type*} [Fintype m] [DecidableEq m]
    (w : m → R) (P : Matrix m n R) (c : n → R) :
    QuadraticMap.weightedSumSquares R w (P *ᵥ c) = (Pᵀ * diagonal w * P).toQuadraticForm' c := by
  rw [toQuadraticForm'_apply, QuadraticMap.weightedSumSquares_apply]
  simp only [transpose_mul_diagonal_mul_apply, mulVec_apply_sum, smul_eq_mul]
  calc ∑ i, w i * ((∑ j, P i j * c j) * ∑ k, P i k * c k)
      = ∑ i, ∑ j, ∑ k, w i * P i j * c j * (P i k * c k) := by
        refine sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine sum_congr rfl fun k _ => ?_
        ring
    _ = ∑ j, ∑ k, ∑ i, w i * P i j * c j * (P i k * c k) := by
        rw [Finset.sum_comm]
        exact sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j, ∑ k, c j * (∑ i, P i j * w i * P i k) * c k := by
        refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine sum_congr rfl fun i _ => ?_
        ring

end MatrixForms

section BaseChange

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Base change of a rational diagonalisation: if the matrix form of `M : Matrix n n ℚ` is
equivalent over `ℚ` to the weighted sum of squares with weights `w`, then the matrix form of the
same matrix read over `ℝ` is equivalent over `ℝ` to the weighted sum of squares with the same
(cast) weights. -/
theorem equivalent_map_of_equivalent (M : Matrix n n ℚ) {m : Type*} [Fintype m] [DecidableEq m]
    (w : m → ℚ)
    (h : QuadraticMap.Equivalent M.toQuadraticForm' (QuadraticMap.weightedSumSquares ℚ w)) :
    QuadraticMap.Equivalent (M.map (algebraMap ℚ ℝ)).toQuadraticForm'
      (QuadraticMap.weightedSumSquares ℝ (fun i => (w i : ℝ))) := by
  obtain ⟨e⟩ := h
  -- the change-of-basis matrix and its inverse, over `ℚ`
  set P : Matrix m n ℚ := LinearMap.toMatrix' (e.toLinearEquiv : (n → ℚ) →ₗ[ℚ] (m → ℚ)) with hP
  set P' : Matrix n m ℚ :=
    LinearMap.toMatrix' (e.toLinearEquiv.symm : (m → ℚ) →ₗ[ℚ] (n → ℚ)) with hP'
  have hPP' : P * P' = 1 := by
    rw [hP, hP', ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    exact LinearMap.ext fun c => by simp
  have hP'P : P' * P = 1 := by
    rw [hP, hP', ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    exact LinearMap.ext fun c => by simp
  -- the rational identity, as an identity of symmetrised matrices
  have hQ : ∀ c : n → ℚ, M.toQuadraticForm' c = (Pᵀ * diagonal w * P).toQuadraticForm' c := by
    intro c
    rw [← weightedSumSquares_mulVec, hP, LinearMap.toMatrix'_mulVec]
    exact (e.map_app c).symm
  have hsym := add_transpose_eq_of_toQuadraticForm'_eq hQ
  -- transport to `ℝ`
  set f : ℚ →+* ℝ := algebraMap ℚ ℝ with hf
  set Pr : Matrix m n ℝ := P.map f with hPr
  set Pr' : Matrix n m ℝ := P'.map f with hPr'
  have hN : (Pᵀ * diagonal w * P).map f =
      Prᵀ * diagonal (fun i => (w i : ℝ)) * Pr := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.diagonal_map (map_zero f)]
    simp only [eq_ratCast]
    rfl
  have hsymr : M.map f + (M.map f)ᵀ =
      Prᵀ * diagonal (fun i => (w i : ℝ)) * Pr + (Prᵀ * diagonal (fun i => (w i : ℝ)) * Pr)ᵀ := by
    have := congrArg (fun A : Matrix n n ℚ => A.map f) hsym
    simpa only [Matrix.map_add f (map_add f), Matrix.transpose_map, hN] using this
  have hQr : ∀ c : n → ℝ,
      (M.map f).toQuadraticForm' c =
        (Prᵀ * diagonal (fun i => (w i : ℝ)) * Pr).toQuadraticForm' c := by
    intro c
    have h1 := congrArg (fun A : Matrix n n ℝ => A.toQuadraticForm' c) hsymr
    simp only [toQuadraticForm'_add, toQuadraticForm'_transpose] at h1
    linarith
  have hPrPr' : Pr * Pr' = 1 := by
    rw [hPr, hPr', ← Matrix.map_mul, hPP']
    exact Matrix.map_one f (map_zero f) (map_one f)
  have hPr'Pr : Pr' * Pr = 1 := by
    rw [hPr, hPr', ← Matrix.map_mul, hP'P]
    exact Matrix.map_one f (map_zero f) (map_one f)
  let er : (n → ℝ) ≃ₗ[ℝ] (m → ℝ) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' Pr) (Matrix.toLin' Pr')
      (by rw [← Matrix.toLin'_mul, hPrPr', Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, hPr'Pr, Matrix.toLin'_one])
  refine ⟨⟨er, fun c => ?_⟩⟩
  change QuadraticMap.weightedSumSquares ℝ (fun i => (w i : ℝ)) (Pr *ᵥ c) = _
  rw [weightedSumSquares_mulVec, hQr]

/-- **Signature is invariant under base change `ℚ → ℝ`** (positive part): the matrix form of a
rational matrix has the same `sigPos` whether read over `ℚ` or over `ℝ`. -/
theorem sigPos_toQuadraticForm'_map (M : Matrix n n ℚ) :
    sigPos (M.map (algebraMap ℚ ℝ)).toQuadraticForm' = sigPos M.toQuadraticForm' := by
  obtain ⟨w, hw⟩ := QuadraticForm.equivalent_weightedSumSquares M.toQuadraticForm'
  rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares hw,
    QuadraticForm.sigPos_of_equiv_weightedSumSquares (equivalent_map_of_equivalent M w hw)]
  congr 1
  ext i
  simp [Rat.cast_pos]

/-- **Signature is invariant under base change `ℚ → ℝ`** (negative part). -/
theorem sigNeg_toQuadraticForm'_map (M : Matrix n n ℚ) :
    sigNeg (M.map (algebraMap ℚ ℝ)).toQuadraticForm' = sigNeg M.toQuadraticForm' := by
  obtain ⟨w, hw⟩ := QuadraticForm.equivalent_weightedSumSquares M.toQuadraticForm'
  rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares hw,
    QuadraticForm.sigNeg_of_equiv_weightedSumSquares (equivalent_map_of_equivalent M w hw)]
  congr 1
  ext i
  simp [Rat.cast_lt_zero]

omit [Fintype n] [DecidableEq n] in
theorem map_ratCast_eq_map_algebraMap (M : Matrix n n ℚ) :
    M.map (Rat.cast : ℚ → ℝ) = M.map (algebraMap ℚ ℝ) := by
  ext i j
  simp

/-- The same, with the real matrix written through `Rat.cast` (the form a concrete instance
usually has). -/
theorem sigPos_toQuadraticForm'_ratCast (M : Matrix n n ℚ) :
    sigPos (M.map (Rat.cast : ℚ → ℝ)).toQuadraticForm' = sigPos M.toQuadraticForm' := by
  rw [map_ratCast_eq_map_algebraMap, sigPos_toQuadraticForm'_map]

theorem sigNeg_toQuadraticForm'_ratCast (M : Matrix n n ℚ) :
    sigNeg (M.map (Rat.cast : ℚ → ℝ)).toQuadraticForm' = sigNeg M.toQuadraticForm' := by
  rw [map_ratCast_eq_map_algebraMap, sigNeg_toQuadraticForm'_map]

end BaseChange

/-! ### Gram matrices: a quadratic form is isometric to the matrix form of its Gram matrix -/

section Gram

variable {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The Gram matrix `(B (b i) (b j))_{i,j}` of a bilinear form in a basis. -/
def gramMatrix (B : LinearMap.BilinForm R V) (b : Module.Basis ι R V) : Matrix ι ι R :=
  Matrix.of fun i j => B (b i) (b j)

@[simp] theorem gramMatrix_apply (B : LinearMap.BilinForm R V) (b : Module.Basis ι R V) (i j : ι) :
    gramMatrix B b i j = B (b i) (b j) := rfl

variable [Fintype ι] [DecidableEq ι]

/-- The quadratic form of a bilinear form is isometric, via the coordinate map of a basis, to the
matrix form of its Gram matrix in that basis. -/
theorem toQuadraticMap_equivalent_gramMatrix (B : LinearMap.BilinForm R V)
    (b : Module.Basis ι R V) :
    QuadraticMap.Equivalent B.toQuadraticMap (gramMatrix B b).toQuadraticForm' := by
  refine ⟨⟨b.equivFun, fun x => ?_⟩⟩
  change (gramMatrix B b).toQuadraticForm' (b.equivFun x) = B.toQuadraticMap x
  rw [toQuadraticForm'_apply, LinearMap.BilinMap.toQuadraticMap_apply]
  conv_rhs => rw [← b.sum_equivFun x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    gramMatrix_apply, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

end Gram

/-! ### T2: the trace Gram matrix of a power basis is a Hermite matrix -/

section PowerBasis

variable {K : Type*} [Field K] [NumberField K] (pb : PowerBasis ℚ K)

/-- The minimal polynomial of the generator of a power basis of `K / ℚ`, read over `ℝ`. -/
def minpolyReal : ℝ[X] := (minpoly ℚ pb.gen).map (algebraMap ℚ ℝ)

theorem natDegree_minpolyReal : (minpolyReal pb).natDegree = pb.dim := by
  rw [minpolyReal, natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective,
    pb.natDegree_minpoly]

theorem croots_minpolyReal : croots (minpolyReal pb) = (minpoly ℚ pb.gen).aroots ℂ := by
  rw [croots, minpolyReal, Polynomial.map_map, aroots_def, ← IsScalarTower.algebraMap_eq]

theorem nodup_croots_minpolyReal : (croots (minpolyReal pb)).Nodup := by
  rw [croots_minpolyReal]
  exact nodup_roots (Polynomial.Separable.map (Algebra.IsSeparable.isSeparable ℚ pb.gen))

/-- The power basis, reindexed by `Fin (minpolyReal pb).natDegree` so that it lines up with
`hermiteMatrix (minpolyReal pb)`. -/
def powBasis : Module.Basis (Fin (minpolyReal pb).natDegree) ℚ K :=
  pb.basis.reindex (finCongr (natDegree_minpolyReal pb).symm)

theorem powBasis_apply (i : Fin (minpolyReal pb).natDegree) :
    powBasis pb i = pb.gen ^ (i : ℕ) := by
  simp [powBasis, Module.Basis.reindex_apply, PowerBasis.coe_basis]

/-- The trace Gram matrix of the power basis: `(i, j) ↦ Tr_{K/ℚ}(θ^(i+j))`. -/
def traceGram : Matrix (Fin (minpolyReal pb).natDegree) (Fin (minpolyReal pb).natDegree) ℚ :=
  Matrix.of fun i j => Algebra.trace ℚ K (pb.gen ^ ((i : ℕ) + (j : ℕ)))

@[simp] theorem traceGram_apply (i j : Fin (minpolyReal pb).natDegree) :
    traceGram pb i j = Algebra.trace ℚ K (pb.gen ^ ((i : ℕ) + (j : ℕ))) := rfl

theorem traceGram_eq_gramMatrix :
    traceGram pb = gramMatrix (Algebra.traceForm ℚ K) (powBasis pb) := by
  ext i j
  rw [traceGram_apply, gramMatrix_apply, Algebra.traceForm_apply, powBasis_apply, powBasis_apply,
    pow_add]

/-- The trace form of `K` is isometric (over `ℚ`) to the matrix form of its Gram matrix in the
power basis. -/
theorem traceForm_equivalent_traceGram :
    QuadraticMap.Equivalent (Algebra.traceForm ℚ K).toQuadraticMap
      (traceGram pb).toQuadraticForm' := by
  rw [traceGram_eq_gramMatrix]
  exact toQuadraticMap_equivalent_gramMatrix _ _

/-- `Tr_{K/ℚ}(θ^k)`, read in `ℝ`, is the `k`-th power sum of the complex roots of the minimal
polynomial of `θ` (the roots are simple, so the multiset sum is the sum over embeddings). -/
theorem trace_pow_eq_powerSum (k : ℕ) :
    algebraMap ℚ ℝ (Algebra.trace ℚ K (pb.gen ^ k)) = powerSum (minpolyReal pb) k := by
  classical
  apply Complex.ofReal_injective
  rw [ofReal_powerSum, croots_minpolyReal, eq_ratCast (algebraMap ℚ ℝ), Complex.ofReal_ratCast,
    ← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings (E := ℂ)]
  simp_rw [map_pow]
  rw [Fintype.sum_equiv pb.liftEquiv' (fun σ => σ pb.gen ^ k) (fun y => (y : ℂ) ^ k)
      (fun σ => by rw [PowerBasis.liftEquiv'_apply_coe]),
    Finset.sum_mem_multiset _ _ (fun y => y ^ k) (fun _ => rfl),
    Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr]
  rw [← croots_minpolyReal]
  exact nodup_croots_minpolyReal pb

/-- The Gram matrix of the trace form in the power basis, read over `ℝ`, is the Hermite matrix
of the minimal polynomial. -/
theorem traceGram_map :
    (traceGram pb).map (algebraMap ℚ ℝ) = hermiteMatrix (minpolyReal pb) := by
  ext i j
  rw [Matrix.map_apply, traceGram_apply, hermiteMatrix_apply]
  exact trace_pow_eq_powerSum pb _

/-- The signature of the trace form is that of the Hermite form of the minimal polynomial. -/
theorem sigPos_traceForm_eq_hermite :
    sigPos (Algebra.traceForm ℚ K).toQuadraticMap = sigPos (hermiteForm (minpolyReal pb)) := by
  rw [(traceForm_equivalent_traceGram pb).sigPos_eq, ← sigPos_toQuadraticForm'_map,
    traceGram_map, hermiteForm_def]

theorem sigNeg_traceForm_eq_hermite :
    sigNeg (Algebra.traceForm ℚ K).toQuadraticMap = sigNeg (hermiteForm (minpolyReal pb)) := by
  rw [(traceForm_equivalent_traceGram pb).sigNeg_eq, ← sigNeg_toQuadraticForm'_map,
    traceGram_map, hermiteForm_def]

/-! ### T3: embeddings ↔ roots; real embeddings ↔ real roots -/

/-- Complex embeddings of `K` correspond to the complex roots of the minimal polynomial of the
generator (`PowerBasis.liftEquiv'`). -/
def embEquivRoot : (K →+* ℂ) ≃ {y : ℂ // y ∈ croots (minpolyReal pb)} :=
  (RingHom.equivRatAlgHom K ℂ).trans
    (pb.liftEquiv'.trans (Equiv.subtypeEquivRight fun y => by rw [croots_minpolyReal]))

theorem embEquivRoot_apply_coe (φ : K →+* ℂ) : (embEquivRoot pb φ : ℂ) = φ pb.gen := by
  simp [embEquivRoot, PowerBasis.liftEquiv'_apply_coe, RingHom.equivRatAlgHom_apply,
    RingHom.toRatAlgHom_apply]

/-- A complex embedding is real iff it sends the generator to a real number. -/
theorem isReal_iff_im_eq_zero (φ : K →+* ℂ) :
    ComplexEmbedding.IsReal φ ↔ (φ pb.gen).im = 0 := by
  rw [ComplexEmbedding.isReal_iff, ← Complex.conj_eq_iff_im]
  constructor
  · intro h
    rw [← ComplexEmbedding.conjugate_coe_eq, h]
  · intro h
    have key : (ComplexEmbedding.conjugate φ).toRatAlgHom = φ.toRatAlgHom :=
      pb.algHom_ext (by simpa [RingHom.toRatAlgHom_apply, ComplexEmbedding.conjugate_coe_eq]
        using h)
    exact (RingHom.equivRatAlgHom K ℂ).injective
      (by rw [RingHom.equivRatAlgHom_apply, RingHom.equivRatAlgHom_apply]; exact key)

/-- The real embeddings are counted by the distinct real roots of the minimal polynomial. -/
theorem card_realRoots_minpolyReal : (realRoots (minpolyReal pb)).card = nrRealPlaces K := by
  classical
  rw [← card_real_embeddings, ← Fintype.card_coe]
  refine (Fintype.card_congr ?_).symm
  refine (Equiv.subtypeEquiv (embEquivRoot pb) fun φ => ?_).trans
    ((Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ croots (minpolyReal pb))
      (fun z : ℂ => z.im = 0)).trans (Equiv.subtypeEquivRight fun z => ?_))
  · rw [isReal_iff_im_eq_zero pb, embEquivRoot_apply_coe]
  · rw [mem_realRoots, mem_distinctRoots]

open scoped Classical in
/-- The non-real embeddings are counted by the distinct non-real roots. -/
theorem card_not_isReal_eq :
    Fintype.card {φ : K →+* ℂ // ¬ ComplexEmbedding.IsReal φ} =
      ((distinctRoots (minpolyReal pb)).filter (fun z => ¬ z.im = 0)).card := by
  classical
  rw [← Fintype.card_coe]
  refine Fintype.card_congr ?_
  refine (Equiv.subtypeEquiv (embEquivRoot pb) fun φ => ?_).trans
    ((Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ croots (minpolyReal pb))
      (fun z : ℂ => ¬ z.im = 0)).trans (Equiv.subtypeEquivRight fun z => ?_))
  · rw [isReal_iff_im_eq_zero pb, embEquivRoot_apply_coe]
  · rw [Finset.mem_filter, mem_distinctRoots]

/-- The complex places are counted by the distinct roots in the upper half plane. -/
theorem card_upperRoots_minpolyReal :
    (upperRoots (minpolyReal pb)).card = nrComplexPlaces K := by
  classical
  have h1 := card_not_isReal_eq pb
  rw [card_complex_embeddings] at h1
  have h2 := Finset.card_filter_add_card_filter_not (s := distinctRoots (minpolyReal pb))
    (fun z : ℂ => z.im = 0)
  have h3 := card_distinctRoots (minpolyReal pb)
  have h4 : realRoots (minpolyReal pb) =
      (distinctRoots (minpolyReal pb)).filter (fun z : ℂ => z.im = 0) := rfl
  rw [h4] at h3
  omega

end PowerBasis

/-! ### T4: the theorem -/

section TraceSignature

variable (K : Type*) [Field K] [NumberField K]

/-- A power basis of `K / ℚ` (primitive element theorem). -/
def primitivePowerBasis : PowerBasis ℚ K := Field.powerBasisOfFiniteOfSeparable ℚ K

/-- **Trace-form signature of a number field** (positive part): `sigPos = r₁ + r₂`. -/
theorem sigPos_traceForm :
    sigPos (Algebra.traceForm ℚ K).toQuadraticMap = nrRealPlaces K + nrComplexPlaces K := by
  rw [sigPos_traceForm_eq_hermite (primitivePowerBasis K), sigPos_hermiteForm,
    card_realRoots_minpolyReal, card_upperRoots_minpolyReal]

/-- **Trace-form signature of a number field** (negative part): `sigNeg = r₂`. -/
theorem sigNeg_traceForm :
    sigNeg (Algebra.traceForm ℚ K).toQuadraticMap = nrComplexPlaces K := by
  rw [sigNeg_traceForm_eq_hermite (primitivePowerBasis K), sigNeg_hermiteForm,
    card_upperRoots_minpolyReal]

/-- **Trace-form signature of a number field** (classical, Hermite–Sylvester; in number-field
form credited to O. Taussky 1968): the trace
form `Tr_{K/ℚ}(x²)` has type `(r₁ + r₂, r₂)`. -/
theorem traceForm_signature :
    sigPos (Algebra.traceForm ℚ K).toQuadraticMap = nrRealPlaces K + nrComplexPlaces K ∧
      sigNeg (Algebra.traceForm ℚ K).toQuadraticMap = nrComplexPlaces K :=
  ⟨sigPos_traceForm K, sigNeg_traceForm K⟩

/-- The trace form is nondegenerate, so its signature fills the dimension: `r₁ + 2 r₂ = [K:ℚ]`,
read off from `sigPos + sigNeg + finrank radical = finrank`. -/
theorem finrank_radical_traceForm :
    Module.finrank ℚ (Algebra.traceForm ℚ K).toQuadraticMap.radical = 0 := by
  have h := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := (Algebra.traceForm ℚ K).toQuadraticMap)
  rw [sigPos_traceForm, sigNeg_traceForm, ← card_add_two_mul_card_eq_rank] at h
  omega

/-- Reading the theorem backwards: the place counts of `K` from its trace-form signature. -/
theorem nrComplexPlaces_eq_sigNeg_traceForm :
    nrComplexPlaces K = sigNeg (Algebra.traceForm ℚ K).toQuadraticMap :=
  (sigNeg_traceForm K).symm

theorem nrRealPlaces_eq_sigPos_sub_sigNeg_traceForm :
    nrRealPlaces K =
      sigPos (Algebra.traceForm ℚ K).toQuadraticMap - sigNeg (Algebra.traceForm ℚ K).toQuadraticMap := by
  rw [sigPos_traceForm, sigNeg_traceForm]
  omega

/-- The same, in the matrix form of the Gram matrix of the trace form in any `ℚ`-basis of `K`
(the shape a concrete instance has: a Hankel matrix of power sums on `Fin n → ℚ`). -/
theorem sigPos_gramMatrix_traceForm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ K) :
    sigPos (gramMatrix (Algebra.traceForm ℚ K) b).toQuadraticForm' =
      nrRealPlaces K + nrComplexPlaces K := by
  rw [← (toQuadraticMap_equivalent_gramMatrix _ b).sigPos_eq, sigPos_traceForm]

theorem sigNeg_gramMatrix_traceForm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ K) :
    sigNeg (gramMatrix (Algebra.traceForm ℚ K) b).toQuadraticForm' = nrComplexPlaces K := by
  rw [← (toQuadraticMap_equivalent_gramMatrix _ b).sigNeg_eq, sigNeg_traceForm]

end TraceSignature

/-! ### T5: positive definite ↔ totally real -/

section PosDef

/-- A quadratic form on a finite-dimensional space over an ordered field is positive definite
iff its positive index of inertia is the whole dimension. -/
theorem posDef_iff_sigPos_eq_finrank {𝕜 M : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup M] [Module 𝕜 M] [FiniteDimensional 𝕜 M]
    (Q : QuadraticForm 𝕜 M) : Q.PosDef ↔ sigPos Q = Module.finrank 𝕜 M := by
  constructor
  · intro h
    apply le_antisymm (sigPos_le_finrank Q)
    have hrestrict : (Q.restrict ⊤).PosDef := fun x hx => by
      rw [QuadraticMap.restrict_apply]
      exact h x (fun hx0 => hx (Subtype.ext hx0))
    simpa [finrank_top] using le_sigPos_of_posDef Q hrestrict
  · intro h
    obtain ⟨V, hV, hpos⟩ := exists_finrank_eq_sigPos_and_posDef Q
    have hV' : V = ⊤ := Submodule.eq_top_of_finrank_eq (hV.trans h)
    subst hV'
    intro x hx
    have := hpos ⟨x, Submodule.mem_top⟩ (fun h0 => hx (congrArg Subtype.val h0))
    rwa [QuadraticMap.restrict_apply] at this

variable (K : Type*) [Field K] [NumberField K]

/-- **Corollary.** The trace form of a number field is positive definite iff the field is
totally real. -/
theorem traceForm_posDef_iff :
    (Algebra.traceForm ℚ K).toQuadraticMap.PosDef ↔ IsTotallyReal K := by
  rw [posDef_iff_sigPos_eq_finrank, sigPos_traceForm, ← card_add_two_mul_card_eq_rank,
    ← nrComplexPlaces_eq_zero_iff]
  omega

end PosDef

end

end HermiteCompositum

