module
public import Mathlib
public import GravityScreening.SignedLieGeneration

@[expose] public section

/-!
# Shared definitions

* `IsBracketCommuting R` — the convention `∀ X Y, R ⁅X, Y⁆ = ⁅X, R Y⁆` for a linear endomorphism of
  a Lie algebra, with its transport along a Lie equivalence.
* `etaSkew η` — the `η`-skew matrices, Mathlib's `skewAdjointMatricesLieSubalgebra (diagonal η)`,
  over a field and any finite index type; `gen η i j`, its generators
  `η j • E i j - η i • E j i`.
* `star0`, `hodgeMat η`, `hodge η` — the Hodge operator on the `η`-skew `4 × 4` matrices, in the
  closed form `X ↦ star0 (diagonal η * X) * diagonal η`.

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

end LorentzLie
