module
public import Mathlib
public import GravityScreening.SignedLieGeneration

@[expose] public section

/-!
# Shared definitions of the Lorentz Lie-algebra library

* `IsBracketCommuting R` — the convention `∀ X Y, R ⁅X, Y⁆ = ⁅X, R Y⁆` for a linear endomorphism of
  a Lie algebra, with its transport along a Lie equivalence.
* `etaSkew η` — the `η`-skew matrices, Mathlib's `skewAdjointMatricesLieSubalgebra (diagonal η)`,
  over a field and any finite index type; `gen η i j`, its generators
  `η j • E i j - η i • E j i`.
* `star0`, `hodgeMat η`, `hodge η` — the Hodge operator on the `η`-skew `4 × 4` matrices, in the
  closed form `X ↦ star0 (diagonal η * X) * diagonal η`; `hodgeMat_eq_hodgeOp`, its agreement with
  `HermitianExclusion.hodgeOp` on the `η4`-skew matrices.
* The explicit matrices the isomorphism statements use: `quat`, `quatBar`, `lam`, `spinPlus`,
  `spinMinus` (signature with product `-1`, and the complex case); `so3Plus`, `so3Minus`
  (definite signature); `splitFrame`, `splitPlus`, `splitMinus` (signature with sum `0`);
  `etaC`, `lamProd`, `hodgeProjPlus`, `hodgeProjMinus` (the two projectors of the Hodge operator
  over `ℂ`); `indefEta` (the diagonal of Mathlib's `so' p q ℝ` read along a bijection).

Every file of this library declares `attribute [local instance] LieRing.ofAssociativeRing`, the
commutator Lie ring structure that `skewAdjointMatricesLieSubalgebra` is stated with.
-/

set_option autoImplicit false

attribute [local instance] LieRing.ofAssociativeRing

namespace LorentzLie

open Matrix

/-! ### The bracket-commuting convention -/

section Convention

variable {K L L' : Type*} [CommRing K] [LieRing L] [LieAlgebra K L] [LieRing L'] [LieAlgebra K L']

/-- A linear endomorphism `R` of a Lie algebra is bracket-commuting when
`R ⁅X, Y⁆ = ⁅X, R Y⁆` for all `X`, `Y`. -/
def IsBracketCommuting (R : L →ₗ[K] L) : Prop :=
  ∀ X Y : L, R ⁅X, Y⁆ = ⁅X, R Y⁆

theorem isBracketCommuting_iff (R : L →ₗ[K] L) :
    IsBracketCommuting R ↔ ∀ X Y : L, R ⁅X, Y⁆ = ⁅X, R Y⁆ :=
  Iff.rfl

/-- The other side of the convention follows by antisymmetry: `R ⁅X, Y⁆ = ⁅R X, Y⁆`. -/
theorem IsBracketCommuting.lie_left {R : L →ₗ[K] L} (hR : IsBracketCommuting R) (X Y : L) :
    R ⁅X, Y⁆ = ⁅R X, Y⁆ := by
  rw [← lie_skew X Y, map_neg, hR Y X, lie_skew]

theorem isBracketCommuting_id : IsBracketCommuting (LinearMap.id : L →ₗ[K] L) :=
  fun _ _ => rfl

theorem IsBracketCommuting.smul {R : L →ₗ[K] L} (hR : IsBracketCommuting R) (c : K) :
    IsBracketCommuting (c • R) := by
  intro X Y
  rw [LinearMap.smul_apply, LinearMap.smul_apply, hR X Y, lie_smul]

theorem IsBracketCommuting.add {R S : L →ₗ[K] L} (hR : IsBracketCommuting R)
    (hS : IsBracketCommuting S) : IsBracketCommuting (R + S) := by
  intro X Y
  rw [LinearMap.add_apply, LinearMap.add_apply, hR X Y, hS X Y, lie_add]

theorem IsBracketCommuting.comp {R S : L →ₗ[K] L} (hR : IsBracketCommuting R)
    (hS : IsBracketCommuting S) : IsBracketCommuting (R ∘ₗ S) := by
  intro X Y
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hS X Y, hR X (S Y)]

/-- Transport along a Lie equivalence `e : L ≃ₗ⁅K⁆ L'`: if `R` is bracket-commuting on `L`, then
`e ∘ R ∘ e⁻¹` is bracket-commuting on `L'`. -/
theorem IsBracketCommuting.lieEquivConj (e : L ≃ₗ⁅K⁆ L') {R : L →ₗ[K] L}
    (hR : IsBracketCommuting R) :
    IsBracketCommuting
      ((e.toLinearEquiv : L →ₗ[K] L') ∘ₗ R ∘ₗ (e.symm.toLinearEquiv : L' →ₗ[K] L)) := by
  intro X Y
  change e (R (e.symm ⁅X, Y⁆)) = ⁅X, e (R (e.symm Y))⁆
  rw [LieEquiv.map_lie, hR, LieEquiv.map_lie, LieEquiv.apply_symm_apply]

/-- Transport along a Lie equivalence, as an equivalence of the two conditions. -/
theorem isBracketCommuting_lieEquivConj_iff (e : L ≃ₗ⁅K⁆ L') (R : L →ₗ[K] L) :
    IsBracketCommuting
        ((e.toLinearEquiv : L →ₗ[K] L') ∘ₗ R ∘ₗ (e.symm.toLinearEquiv : L' →ₗ[K] L)) ↔
      IsBracketCommuting R := by
  refine ⟨fun h => ?_, fun h => h.lieEquivConj e⟩
  intro X Y
  have h1 := h (e X) (e Y)
  change e (R (e.symm ⁅e X, e Y⁆)) = ⁅e X, e (R (e.symm (e Y)))⁆ at h1
  rw [← LieEquiv.map_lie, LieEquiv.symm_apply_apply, LieEquiv.symm_apply_apply,
    ← LieEquiv.map_lie] at h1
  exact e.injective h1

end Convention

/-! ### The `η`-skew matrices and their generators -/

section EtaSkew

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The `η`-skew matrices for the diagonal form `diagonal η`: the matrices `X` with
`Xᵀ * diagonal η = diagonal η * (-X)`. This is Mathlib's
`skewAdjointMatricesLieSubalgebra (Matrix.diagonal η)`. -/
abbrev etaSkew (η : ι → K) : LieSubalgebra K (Matrix ι ι K) :=
  skewAdjointMatricesLieSubalgebra (Matrix.diagonal η)

/-- Membership in `etaSkew η`, entry by entry: `X j i * η j = -(η i * X i j)`. -/
theorem mem_etaSkew_iff (η : ι → K) (X : Matrix ι ι K) :
    X ∈ etaSkew η ↔ ∀ i j, X j i * η j = -(η i * X i j) := by
  rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  unfold Matrix.IsSkewAdjoint Matrix.IsAdjointPair
  constructor
  · intro h i j
    have h1 := congrFun (congrFun h i) j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using h1
  · intro h
    ext i j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using h i j

/-- The matrix `η j • E i j - η i • E j i` (`GravityScreening.SignedLieGeneration.skew η i j`) is
`η`-skew. -/
theorem skew_mem_etaSkew (η : ι → K) (i j : ι) :
    GravityScreening.SignedLieGeneration.skew η i j ∈ etaSkew η := by
  rw [mem_etaSkew_iff]
  intro a b
  simp only [GravityScreening.SignedLieGeneration.skew, Matrix.sub_apply, Matrix.single_apply]
  by_cases h1 : i = b <;> by_cases h2 : j = a <;> by_cases h3 : j = b <;> by_cases h4 : i = a <;>
    simp_all

/-- The generator `gen η i j = η j • E i j - η i • E j i` of the `η`-skew matrices. -/
def gen (η : ι → K) (i j : ι) : etaSkew η :=
  ⟨GravityScreening.SignedLieGeneration.skew η i j, skew_mem_etaSkew η i j⟩

@[simp] theorem gen_coe (η : ι → K) (i j : ι) :
    (gen η i j : Matrix ι ι K) = Matrix.single i j (η j) - Matrix.single j i (η i) :=
  rfl

end EtaSkew

/-! ### The Hodge operator in dimension four -/

section Hodge

variable {K : Type*} [Field K]

/-- The metric-free complement on `4 × 4` matrices, with `ε₀₁₂₃ = +1`: the entry at `(k, l)` is
the signed entry of `A` at the complementary pair of indices. Only the entries of `A` above the
diagonal are used. -/
def star0 (A : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, A 2 3, -A 1 3, A 1 2;  -A 2 3, 0, A 0 3, -A 0 2;
     A 1 3, -A 0 3, 0, A 0 1;  -A 1 2, A 0 2, -A 0 1, 0]

/-- The Hodge operator on `4 × 4` matrices in closed form:
`hodgeMat η X = star0 (diagonal η * X) * diagonal η`. -/
def hodgeMat (η : Fin 4 → K) (X : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 4) (Fin 4) K :=
  star0 (Matrix.diagonal η * X) * Matrix.diagonal η

theorem star0_transpose (A : Matrix (Fin 4) (Fin 4) K) : (star0 A)ᵀ = -star0 A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [star0]

theorem star0_add (A B : Matrix (Fin 4) (Fin 4) K) : star0 (A + B) = star0 A + star0 B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [star0] <;> ring

theorem star0_smul (c : K) (A : Matrix (Fin 4) (Fin 4) K) : star0 (c • A) = c • star0 A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [star0]

theorem hodgeMat_add (η : Fin 4 → K) (X Y : Matrix (Fin 4) (Fin 4) K) :
    hodgeMat η (X + Y) = hodgeMat η X + hodgeMat η Y := by
  simp only [hodgeMat, Matrix.mul_add, star0_add, Matrix.add_mul]

theorem hodgeMat_smul (η : Fin 4 → K) (c : K) (X : Matrix (Fin 4) (Fin 4) K) :
    hodgeMat η (c • X) = c • hodgeMat η X := by
  simp only [hodgeMat, Matrix.mul_smul, star0_smul, Matrix.smul_mul]

/-- `hodgeMat η` maps every matrix to an `η`-skew matrix (no hypothesis on `η`): `star0` takes
values in the antisymmetric matrices, and `S * diagonal η` is `η`-skew for antisymmetric `S`. -/
theorem hodgeMat_mem_etaSkew (η : Fin 4 → K) (X : Matrix (Fin 4) (Fin 4) K) :
    hodgeMat η X ∈ etaSkew η := by
  rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  unfold Matrix.IsSkewAdjoint Matrix.IsAdjointPair
  rw [hodgeMat, Matrix.transpose_mul, Matrix.diagonal_transpose, star0_transpose]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

/-- The Hodge operator on the `η`-skew `4 × 4` matrices, `X ↦ star0 (diagonal η * X) * diagonal η`,
as a linear endomorphism of `etaSkew η`. -/
def hodge (η : Fin 4 → K) : etaSkew η →ₗ[K] etaSkew η where
  toFun X := ⟨hodgeMat η X.1, hodgeMat_mem_etaSkew η X.1⟩
  map_add' X Y := Subtype.ext (hodgeMat_add η X.1 Y.1)
  map_smul' c X := Subtype.ext (hodgeMat_smul η c X.1)

@[simp] theorem hodge_coe (η : Fin 4 → K) (X : etaSkew η) :
    (hodge η X : Matrix (Fin 4) (Fin 4) K) = hodgeMat η X :=
  rfl

end Hodge

/-! ### Explicit matrices for the isomorphism statements -/

section Explicit

/-- `sl(2, ℂ)`. -/
abbrev sl2C := LieAlgebra.SpecialLinear.sl (Fin 2) ℂ

/-- `sl(2, ℝ)`. -/
abbrev sl2R := LieAlgebra.SpecialLinear.sl (Fin 2) ℝ

/-- `so(3)`: the skew-symmetric real `3 × 3` matrices. -/
abbrev so3 := LieAlgebra.Orthogonal.so (Fin 3) ℝ

/-- `sl(2, ℂ)` as a real Lie algebra. -/
abbrev sl2CReal := RestrictScalars ℝ ℂ sl2C

/-- The underlying complex `2 × 2` matrix of an element of `sl2CReal`. -/
def sl2CRealMat (x : sl2CReal) : Matrix (Fin 2) (Fin 2) ℂ :=
  (RestrictScalars.addEquiv ℝ ℂ sl2C x).1

/-- The quaternion units as complex `2 × 2` matrices: `(1, i σ₁, i σ₂, i σ₃)`. -/
def quat : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![1, 0; 0, 1], !![0, Complex.I; Complex.I, 0], !![0, 1; -1, 0],
    !![Complex.I, 0; 0, -Complex.I]]

/-- The conjugate quaternion units: `(1, -i σ₁, -i σ₂, -i σ₃)`. -/
def quatBar : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![1, 0; 0, 1], !![0, -Complex.I; -Complex.I, 0], !![0, -1; 1, 0],
    !![-Complex.I, 0; 0, Complex.I]]

/-- A square root of a sign: `lam 1 = 1`, `lam (-1) = i`. -/
noncomputable def lam (s : ℝ) : ℂ := ((1 + s) / 2 : ℝ) + ((1 - s) / 2 : ℝ) * Complex.I

/-- `spinPlus η i j = ½ · lam (η i) · lam (η j) · quat i · quatBar j`. -/
noncomputable def spinPlus (η : Fin 4 → ℝ) (i j : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 / 2 : ℂ) * lam (η i) * lam (η j)) • (quat i * quatBar j)

/-- `spinMinus η i j = ½ · lam (η i) · lam (η j) · quatBar i · quat j`. -/
noncomputable def spinMinus (η : Fin 4 → ℝ) (i j : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 / 2 : ℂ) * lam (η i) * lam (η j)) • (quatBar i * quat j)

/-- The skew-symmetric `3 × 3` matrix with entries `(c₁, c₂, c₃) = (X 0 1 - X 2 3, X 0 2 + X 1 3,
X 0 3 - X 1 2)`. -/
def so3Plus (X : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -(X 0 3 - X 1 2), X 0 2 + X 1 3;
     X 0 3 - X 1 2, 0, -(X 0 1 - X 2 3);
     -(X 0 2 + X 1 3), X 0 1 - X 2 3, 0]

/-- The skew-symmetric `3 × 3` matrix with entries `(c₁, c₂, c₃) = (-X 0 1 - X 2 3,
-X 0 2 + X 1 3, -X 0 3 - X 1 2)`. -/
def so3Minus (X : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -(-X 0 3 - X 1 2), -X 0 2 + X 1 3;
     -X 0 3 - X 1 2, 0, -(-X 0 1 - X 2 3);
     -(-X 0 2 + X 1 3), -X 0 1 - X 2 3, 0]

open Classical in
/-- A frame of real `2 × 2` matrices with `det (splitFrame η i) = η i` for a signature with two
entries `1` and two entries `-1`: the first index with `η i = 1` gets the identity, the second
gets `!![0, -1; 1, 0]`; the first index with `η i ≠ 1` gets `!![0, 1; 1, 0]`, the second gets
`!![1, 0; 0, -1]`. -/
noncomputable def splitFrame (η : Fin 4 → ℝ) (i : Fin 4) : Matrix (Fin 2) (Fin 2) ℝ :=
  if η i = 1 then
    (if ∃ j, j < i ∧ η j = 1 then !![0, -1; 1, 0] else !![1, 0; 0, 1])
  else
    (if ∃ j, j < i ∧ η j ≠ 1 then !![1, 0; 0, -1] else !![0, 1; 1, 0])

/-- `splitPlus η i j = ½ · splitFrame η i · adjugate (splitFrame η j)`. -/
noncomputable def splitPlus (η : Fin 4 → ℝ) (i j : Fin 4) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / 2 : ℝ) • (splitFrame η i * (splitFrame η j).adjugate)

/-- `splitMinus η i j = ½ · adjugate (splitFrame η i) · splitFrame η j`. -/
noncomputable def splitMinus (η : Fin 4 → ℝ) (i j : Fin 4) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / 2 : ℝ) • ((splitFrame η i).adjugate * splitFrame η j)

/-- A real diagonal form read over `ℂ`: `etaC η = fun i => (η i : ℂ)` (reducible). -/
abbrev etaC (η : Fin 4 → ℝ) : Fin 4 → ℂ := fun i => (η i : ℂ)

/-- The diagonal of Mathlib's `LieAlgebra.Orthogonal.indefiniteDiagonal p q ℝ` (entries `1` on
`p`, `-1` on `q`), read along a bijection `e : p ⊕ q ≃ ι`. -/
def indefEta {p q ι : Type*} (e : p ⊕ q ≃ ι) : ι → ℝ :=
  fun i => Sum.elim (fun _ => (1 : ℝ)) (fun _ => (-1 : ℝ)) (e.symm i)

/-- `lamProd η = ∏ i, lam (η i)`; for entries `±1` its square is `∏ i, η i`. -/
noncomputable def lamProd (η : Fin 4 → ℝ) : ℂ := ∏ i, lam (η i)

/-- The projector `½ (1 + (lamProd η)⁻¹ • hodge)` of the Hodge operator over `ℂ`. Under
`etaSkewCEquiv` its image is the second factor. -/
noncomputable def hodgeProjPlus (η : Fin 4 → ℝ) : etaSkew (etaC η) →ₗ[ℂ] etaSkew (etaC η) :=
  (1 / 2 : ℂ) • (LinearMap.id + (lamProd η)⁻¹ • hodge (etaC η))

/-- The projector `½ (1 - (lamProd η)⁻¹ • hodge)` of the Hodge operator over `ℂ`. -/
noncomputable def hodgeProjMinus (η : Fin 4 → ℝ) : etaSkew (etaC η) →ₗ[ℂ] etaSkew (etaC η) :=
  (1 / 2 : ℂ) • (LinearMap.id - (lamProd η)⁻¹ • hodge (etaC η))

/-- Sanity: `lam 1 = 1`. -/
theorem lam_one : lam 1 = 1 := by simp [lam]

/-- Sanity: `lam (-1) = i`. -/
theorem lam_neg_one : lam (-1) = Complex.I := by
  simp [lam]

/-- Sanity: `lam s ^ 2 = s` for `s = ±1`. -/
theorem lam_sq (s : ℝ) (hs : s = 1 ∨ s = -1) : lam s ^ 2 = (s : ℂ) := by
  rcases hs with rfl | rfl
  · simp [lam_one]
  · simp [lam_neg_one]

end Explicit

end LorentzLie
