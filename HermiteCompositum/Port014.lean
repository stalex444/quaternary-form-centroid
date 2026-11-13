module
public import Mathlib
public import HermiteCompositum.Defs

@[expose] public section
/-!
# Port of the registered entry PALOMAR-2026-09-02-000014 (the parts the degree-12 instance needs)

**Everything in this file is PORTED from the registered Palomar entry
PALOMAR-2026-09-02-000014** ("golden-family trace forms", Lean v4.31.0 / Mathlib `fabf563a`) to
the present pin (Lean v4.35.0-rc2 / Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`).
Nothing here is claimed as new; each theorem keeps its original name inside the namespace
`HermiteCompositum.Port014`, and each section docstring below names the source file of 000014
it comes from. The declarations of the port that the compared statements reach (`fQ`, `fρ`
with their monicity and degree, and the irreducibility of `X³−X−1` and `X⁴−X−1` over `ℤ` and
`ℚ`) are not in this file but in `HermiteCompositum/Defs.lean`, which `Challenge.lean` repeats
byte for byte. Edits relative to 000014, none of which changes a statement: the one-line
`ZMod 2` fix in `quartic_irred_zmod2` made when the port was first compiled at this pin; an
`omega` step replaced by an explicit term in `cubic_irred_zmod2`, `monic_deg2_no_root_eq` and
`quartic_irred_zmod2` (all three in `Defs.lean`, where a comment gives the reason); and the
local `attribute [-instance]` line below.

Contents (namespace `PDT` ↦ `HermiteCompositum.Port014`; verbatim except for those edits):
* `PdtSignature`, `PdtSignatureRho` — the Hankel (power-sum) Gram matrices `M` (quartic) and `Mρ`
  (cubic), their determinants `−283` and `−23`, explicit rational congruences to diagonal form,
  and the concrete Sylvester statements `signature_3_1`, `signature_2_1`.
* `PdtTraceLink` — `M`, `Mρ` ARE the trace-form Gram matrices of `ℚ[X]/(X⁴−X−1)` and
  `ℚ[X]/(X³−X−1)` in the power bases; the power sums `tQ0 … tQ6`, `tρ0 … tρ4`; the power-basis
  discriminants `discr_Q = −283`, `discr_ρ = −23` (at the ℚ level).
* `PdtTraceSignature` — the intrinsic signatures `sigPos/sigNeg` of the trace forms: `(3,1)`
  for the quartic field and `(2,1)` for the cubic field.
* `PdtIrreducible` — irreducibility of `X³−X−1` and `X⁴−X−1` over `ℤ` and `ℚ` (reduction mod 2);
  in `Defs.lean`, except `quad_irred_zmod2`, which is here.
* Two two-line consequences from 000014's `PdtTraceTensor` instance section, `discr_bρ` and
  `discr_bQ` (the discriminants of the reindexed bases `bρ`, `bQ`).

Not ported: 000014's tensor-product / compositum sections (`PdtTraceCompositum`,
`PdtTraceTensor`, `TraceForms`) — the present entry takes the compositum as a tower of fields
instead (see `HermiteCompositum.Instance`).
-/

-- `HermiteCompositum.Defs` also declares the instance `Fact (Irreducible fρ)`, which the tower `L`
-- needs. This file treats `AdjoinRoot fρ` only as a `ℚ`-algebra, as the registered entry did, so
-- the instance is switched off here (locally; importers of this file still see it).
attribute [-instance] HermiteCompositum.Instance.instFactIrreduciblePolynomialRatFρ

namespace HermiteCompositum.Port014

open Matrix

/-- The trace-form Gram matrix of `K = ℚ[x]/(x⁴ − x − 1)` in the power basis. -/
def M : Matrix (Fin 4) (Fin 4) ℚ :=
  !![4,0,0,3; 0,0,3,4; 0,3,4,0; 3,4,0,3]

/-- The explicit rational congruence matrix (symmetric Gaussian elimination
with a permutation to dodge the zero leading 2×2 minor). -/
def P : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 0, -3/4;
     0, 0, 1, 16/9;
     0, 1, -3/4, -4/3;
     0, 0, 0, 1]

/-- The diagonalised trace form `D = Pᵀ M P`. -/
def D : Matrix (Fin 4) (Fin 4) ℚ :=
  !![4, 0, 0, 0;
     0, 4, 0, 0;
     0, 0, -9/4, 0;
     0, 0, 0, 283/36]

/-- `M` is symmetric (it is a Gram matrix). -/
theorem M_symm : M.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M, Matrix.IsSymm, Matrix.transpose_apply]

/-- The determinant of the trace form is `-283`. Negative determinant forces
an odd number of negative eigenvalues, hence at least one. -/
theorem det_M : M.det = -283 := by
  simp only [M, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.det_fin_zero, Matrix.submatrix_apply, Fin.succAbove, Fin.castSucc_zero,
    Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  decide +kernel

/-- `det M < 0`. -/
theorem det_M_neg : M.det < 0 := by
  rw [det_M]; norm_num

/-- The congruence `Pᵀ * M * P = D` holds exactly over `ℚ`. -/
theorem congruence : P.transpose * M * P = D := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P, M, D, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] <;> norm_num

/-- `P` is invertible: its determinant is `-1`. -/
theorem det_P : P.det = -1 := by
  simp only [P, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.det_fin_zero, Matrix.submatrix_apply, Fin.succAbove, Fin.castSucc_zero,
    Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  decide +kernel

/-- `P` is a unit (its determinant is a unit), so the congruence is genuine. -/
theorem P_isUnit : IsUnit P.det := by
  rw [det_P]; exact isUnit_one.neg

/-- `D` is diagonal. -/
theorem D_isDiag : D.IsDiag := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [D]

/-! ### The (3,1) signature, read off from the signs of the diagonal of `D`. -/

theorem D00_pos : (0 : ℚ) < D 0 0 := by show (0 : ℚ) < (4 : ℚ); norm_num
theorem D11_pos : (0 : ℚ) < D 1 1 := by show (0 : ℚ) < (4 : ℚ); norm_num
theorem D33_pos : (0 : ℚ) < D 3 3 := by show (0 : ℚ) < (283 / 36 : ℚ); norm_num
theorem D22_neg : D 2 2 < (0 : ℚ) := by show (-9 / 4 : ℚ) < 0; norm_num

/-- **The (3,1) signature theorem (concrete Sylvester form).**

There is an invertible rational congruence `P` carrying the trace form `M`
to the diagonal form `D` whose diagonal has exactly three positive entries
and one negative entry. By Sylvester's law of inertia the signature of the
real quadratic form `M` is therefore `(3, 1)`. Together with `det_M = -283`
(`< 0`, forcing an odd number of negative signs) this pins the signature
uniquely. -/
theorem signature_3_1 :
    M.IsSymm ∧
    P.transpose * M * P = D ∧
    IsUnit P.det ∧
    D.IsDiag ∧
    (0 < D 0 0 ∧ 0 < D 1 1 ∧ 0 < D 3 3) ∧ D 2 2 < 0 ∧
    M.det = -283 := by
  exact ⟨M_symm, congruence, P_isUnit, D_isDiag,
    ⟨D00_pos, D11_pos, D33_pos⟩, D22_neg, det_M⟩

end HermiteCompositum.Port014

-- ===== PdtSignatureRho (ported from PALOMAR-2026-09-02-000014) =====

namespace HermiteCompositum.Port014
open Matrix

/-!
# The (2,1) signature of the trace form of K = ℚ[x]/(x³ − x − 1)  (the ρ / 3-space side)

Companion to `PdtSignature` (the quartic Q / 4D side, signature (3,1)). The cubic
ρ = real root of x³ − x − 1 governs 3-space; its trace form has signature (2,1).
Power sums of the roots (Newton, e₁=0, e₂=−1, e₃=1): p₀=3, p₁=0, p₂=2, p₃=3, p₄=2,
so the Gram matrix in the power basis {1,x,x²} is `Mρ = !![3,0,2; 0,2,3; 2,3,2]`
(Mρ_{ij} = p_{i+j}). We prove, all kernel-checked: `det Mρ = −23 = disc(x³−x−1)`,
and an explicit ℚ-congruence `Pρᵀ Mρ Pρ = Dρ = diag(3, 2, −23/6)` with two positive
and one negative diagonal entry, so by Sylvester's law the signature is (2,1).
-/

def Mρ : Matrix (Fin 3) (Fin 3) ℚ := !![3,0,2; 0,2,3; 2,3,2]
def Pρ : Matrix (Fin 3) (Fin 3) ℚ := !![1,0,-2/3; 0,1,-3/2; 0,0,1]
def Dρ : Matrix (Fin 3) (Fin 3) ℚ := !![3,0,0; 0,2,0; 0,0,-23/6]

theorem Mρ_symm : Mρ.IsSymm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Mρ, Matrix.transpose_apply]

theorem detMρ : Mρ.det = -23 := by
  simp [Matrix.det_fin_three, Mρ]; norm_num

theorem detMρ_neg : Mρ.det < 0 := by rw [detMρ]; norm_num

theorem congruenceρ : Pρ.transpose * Mρ * Pρ = Dρ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pρ, Mρ, Dρ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;> norm_num

theorem detPρ : Pρ.det = 1 := by
  simp [Matrix.det_fin_three, Pρ]

theorem Pρ_isUnit : IsUnit Pρ.det := by rw [detPρ]; exact isUnit_one

theorem Dρ_isDiag : Dρ.IsDiag := by
  intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [Dρ]

theorem Dρ00_pos : (0:ℚ) < Dρ 0 0 := by show (0:ℚ) < 3; norm_num
theorem Dρ11_pos : (0:ℚ) < Dρ 1 1 := by show (0:ℚ) < 2; norm_num
theorem Dρ22_neg : Dρ 2 2 < (0:ℚ) := by show (-23/6:ℚ) < 0; norm_num

/-- **The (2,1) signature theorem (ρ / 3-space side).** An explicit invertible ℚ-congruence
carries the trace form `Mρ` to `diag(3, 2, −23/6)` (two positive, one negative); with
`det Mρ = −23 < 0` (odd # of negative signs) this pins the signature as (2,1) by Sylvester. -/
theorem signature_2_1 :
    Mρ.IsSymm ∧ Pρ.transpose * Mρ * Pρ = Dρ ∧ IsUnit Pρ.det ∧ Dρ.IsDiag ∧
    (0 < Dρ 0 0 ∧ 0 < Dρ 1 1) ∧ Dρ 2 2 < 0 ∧ Mρ.det = -23 :=
  ⟨Mρ_symm, congruenceρ, Pρ_isUnit, Dρ_isDiag, ⟨Dρ00_pos, Dρ11_pos⟩, Dρ22_neg, detMρ⟩

end HermiteCompositum.Port014

-- ===== PdtTraceLink (ported from PALOMAR-2026-09-02-000014) =====

/-!
# The integer matrices `M` and `Mρ` are the trace-form Gram matrices

`PdtSignature` fixes the integer matrix

  `M = !![4,0,0,3; 0,0,3,4; 0,3,4,0; 3,4,0,3]`,  `det M = -283`,

and `PdtSignatureRho` fixes

  `Mρ = !![3,0,2; 0,2,3; 2,3,2]`,  `det Mρ = -23`.

Both are introduced there by hand, with Newton's identities quoted in a
comment. This file *proves* the link: `M` and `Mρ` really are the Gram
matrices of the trace form `(x, y) ↦ Tr_{K/ℚ}(x y)` in the power basis
`1, r, r², …` of `K = ℚ[X]/(f)` for `f = X⁴ − X − 1` resp. `X³ − X − 1`,
and their determinants are the power-basis discriminants `Algebra.discr`.

Everything is done with `AdjoinRoot`, `PowerBasis` and `Algebra.traceMatrix`.
-/

namespace HermiteCompositum.Port014

open Polynomial Module

/-! ### The two polynomials -/

-- `fQ`, `fρ`, `fQ_monic`, `fρ_monic`, `fQ_natDegree` and `fρ_natDegree` are in
-- `HermiteCompositum/Defs.lean` (shared verbatim with `Challenge.lean`).

/-! ### The power bases -/

/-- The power basis `1, r, r², r³` of `ℚ[X]/(X⁴ − X − 1)`. -/
noncomputable def pbQ : PowerBasis ℚ (AdjoinRoot fQ) := AdjoinRoot.powerBasis' fQ_monic

/-- The power basis `1, r, r²` of `ℚ[X]/(X³ − X − 1)`. -/
noncomputable def pbρ : PowerBasis ℚ (AdjoinRoot fρ) := AdjoinRoot.powerBasis' fρ_monic

theorem pbQ_dim : pbQ.dim = 4 := fQ_natDegree

theorem pbρ_dim : pbρ.dim = 3 := fρ_natDegree

theorem pbQ_gen : pbQ.gen = AdjoinRoot.root fQ := rfl

theorem pbρ_gen : pbρ.gen = AdjoinRoot.root fρ := rfl

/-! ### The defining relations satisfied by the roots -/

theorem rQ_pow_four : (AdjoinRoot.root fQ) ^ 4 = AdjoinRoot.root fQ + 1 := by
  have h : (Polynomial.aeval (AdjoinRoot.root fQ)) fQ = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have h2 : (Polynomial.aeval (AdjoinRoot.root fQ)) (X ^ 4 - X - 1 : ℚ[X]) = 0 := h
  simp only [map_sub, map_pow, map_one, Polynomial.aeval_X] at h2
  linear_combination h2

theorem rρ_pow_three : (AdjoinRoot.root fρ) ^ 3 = AdjoinRoot.root fρ + 1 := by
  have h : (Polynomial.aeval (AdjoinRoot.root fρ)) fρ = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have h2 : (Polynomial.aeval (AdjoinRoot.root fρ)) (X ^ 3 - X - 1 : ℚ[X]) = 0 := h
  simp only [map_sub, map_pow, map_one, Polynomial.aeval_X] at h2
  linear_combination h2

theorem rQ_pow_five :
    (AdjoinRoot.root fQ) ^ 5 = (AdjoinRoot.root fQ) ^ 2 + AdjoinRoot.root fQ := by
  linear_combination (AdjoinRoot.root fQ) * rQ_pow_four

theorem rQ_pow_six :
    (AdjoinRoot.root fQ) ^ 6 = (AdjoinRoot.root fQ) ^ 3 + (AdjoinRoot.root fQ) ^ 2 := by
  linear_combination (AdjoinRoot.root fQ) ^ 2 * rQ_pow_four

theorem rρ_pow_four :
    (AdjoinRoot.root fρ) ^ 4 = (AdjoinRoot.root fρ) ^ 2 + AdjoinRoot.root fρ := by
  linear_combination (AdjoinRoot.root fρ) * rρ_pow_three

/-! ### The power bases, reindexed by `Fin 4` and `Fin 3` -/

/-- The power basis of `ℚ[X]/(X⁴ − X − 1)`, indexed by `Fin 4`. -/
noncomputable def bQ : Basis (Fin 4) ℚ (AdjoinRoot fQ) :=
  pbQ.basis.reindex (finCongr pbQ_dim)

/-- The power basis of `ℚ[X]/(X³ − X − 1)`, indexed by `Fin 3`. -/
noncomputable def bρ : Basis (Fin 3) ℚ (AdjoinRoot fρ) :=
  pbρ.basis.reindex (finCongr pbρ_dim)

theorem bQ_apply (i : Fin 4) : bQ i = AdjoinRoot.root fQ ^ (i : ℕ) := by
  show (pbQ.basis.reindex (finCongr pbQ_dim)) i = _
  rw [Basis.reindex_apply, pbQ.basis_eq_pow, pbQ_gen]
  simp

theorem bρ_apply (i : Fin 3) : bρ i = AdjoinRoot.root fρ ^ (i : ℕ) := by
  show (pbρ.basis.reindex (finCongr pbρ_dim)) i = _
  rw [Basis.reindex_apply, pbρ.basis_eq_pow, pbρ_gen]
  simp

theorem bQ0 : bQ 0 = 1 := by simp [bQ_apply]
theorem bQ1 : bQ 1 = AdjoinRoot.root fQ := by simp [bQ_apply]
theorem bQ2 : bQ 2 = AdjoinRoot.root fQ ^ 2 := by simp [bQ_apply]
theorem bQ3 : bQ 3 = AdjoinRoot.root fQ ^ 3 := by simp [bQ_apply]

theorem bρ0 : bρ 0 = 1 := by simp [bρ_apply]
theorem bρ1 : bρ 1 = AdjoinRoot.root fρ := by simp [bρ_apply]
theorem bρ2 : bρ 2 = AdjoinRoot.root fρ ^ 2 := by simp [bρ_apply]

/-! ### The trace, expanded in the power basis -/

theorem traceQ_eq (x : AdjoinRoot fQ) :
    Algebra.trace ℚ (AdjoinRoot fQ) x
      = bQ.repr (x * bQ 0) 0 + bQ.repr (x * bQ 1) 1
        + bQ.repr (x * bQ 2) 2 + bQ.repr (x * bQ 3) 3 := by
  rw [Algebra.trace_eq_matrix_trace bQ x]
  simp only [Matrix.trace, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Fin.sum_univ_four]

theorem traceρ_eq (x : AdjoinRoot fρ) :
    Algebra.trace ℚ (AdjoinRoot fρ) x
      = bρ.repr (x * bρ 0) 0 + bρ.repr (x * bρ 1) 1 + bρ.repr (x * bρ 2) 2 := by
  rw [Algebra.trace_eq_matrix_trace bρ x]
  simp only [Matrix.trace, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Fin.sum_univ_three]

/-! ### The higher powers of the root, expanded in the power basis -/

theorem powQ4 : AdjoinRoot.root fQ ^ 4 = bQ 0 + bQ 1 := by
  rw [bQ0, bQ1]; linear_combination rQ_pow_four

theorem powQ5 : AdjoinRoot.root fQ ^ 5 = bQ 1 + bQ 2 := by
  rw [bQ1, bQ2]; linear_combination rQ_pow_five

theorem powQ6 : AdjoinRoot.root fQ ^ 6 = bQ 2 + bQ 3 := by
  rw [bQ2, bQ3]; linear_combination rQ_pow_six

theorem powρ3 : AdjoinRoot.root fρ ^ 3 = bρ 0 + bρ 1 := by
  rw [bρ0, bρ1]; linear_combination rρ_pow_three

theorem powρ4 : AdjoinRoot.root fρ ^ 4 = bρ 1 + bρ 2 := by
  rw [bρ1, bρ2]; linear_combination rρ_pow_four

/-! ### The power sums `p_k = Tr(r^k)` -/

theorem tQ0 : Algebra.trace ℚ (AdjoinRoot fQ) 1 = 4 := by
  simpa using Algebra.trace_algebraMap_of_basis bQ (1 : ℚ)

theorem tQ1 : Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ) = 0 := by
  rw [traceQ_eq]
  have e0 : AdjoinRoot.root fQ * bQ 0 = bQ 1 := by rw [bQ0, bQ1]; ring
  have e1 : AdjoinRoot.root fQ * bQ 1 = bQ 2 := by rw [bQ1, bQ2]; ring
  have e2 : AdjoinRoot.root fQ * bQ 2 = bQ 3 := by rw [bQ2, bQ3]; ring
  have e3 : AdjoinRoot.root fQ * bQ 3 = bQ 0 + bQ 1 := by rw [← powQ4, bQ3]; ring
  rw [e0, e1, e2, e3]
  simp

theorem tQ2 : Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ ^ 2) = 0 := by
  rw [traceQ_eq]
  have e0 : AdjoinRoot.root fQ ^ 2 * bQ 0 = bQ 2 := by rw [bQ0, bQ2]; ring
  have e1 : AdjoinRoot.root fQ ^ 2 * bQ 1 = bQ 3 := by rw [bQ1, bQ3]; ring
  have e2 : AdjoinRoot.root fQ ^ 2 * bQ 2 = bQ 0 + bQ 1 := by rw [← powQ4, bQ2]; ring
  have e3 : AdjoinRoot.root fQ ^ 2 * bQ 3 = bQ 1 + bQ 2 := by rw [← powQ5, bQ3]; ring
  rw [e0, e1, e2, e3]
  simp

theorem tQ3 : Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ ^ 3) = 3 := by
  rw [traceQ_eq]
  have e0 : AdjoinRoot.root fQ ^ 3 * bQ 0 = bQ 3 := by rw [bQ0, bQ3]; ring
  have e1 : AdjoinRoot.root fQ ^ 3 * bQ 1 = bQ 0 + bQ 1 := by rw [← powQ4, bQ1]; ring
  have e2 : AdjoinRoot.root fQ ^ 3 * bQ 2 = bQ 1 + bQ 2 := by rw [← powQ5, bQ2]; ring
  have e3 : AdjoinRoot.root fQ ^ 3 * bQ 3 = bQ 2 + bQ 3 := by rw [← powQ6, bQ3]; ring
  rw [e0, e1, e2, e3]
  simp
  norm_num

theorem tQ4 : Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ ^ 4) = 4 := by
  rw [rQ_pow_four, map_add, tQ1, tQ0]; norm_num

theorem tQ5 : Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ ^ 5) = 0 := by
  rw [rQ_pow_five, map_add, tQ2, tQ1]; norm_num

theorem tQ6 : Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ ^ 6) = 3 := by
  rw [rQ_pow_six, map_add, tQ3, tQ2]; norm_num

theorem tρ0 : Algebra.trace ℚ (AdjoinRoot fρ) 1 = 3 := by
  simpa using Algebra.trace_algebraMap_of_basis bρ (1 : ℚ)

theorem tρ1 : Algebra.trace ℚ (AdjoinRoot fρ) (AdjoinRoot.root fρ) = 0 := by
  rw [traceρ_eq]
  have e0 : AdjoinRoot.root fρ * bρ 0 = bρ 1 := by rw [bρ0, bρ1]; ring
  have e1 : AdjoinRoot.root fρ * bρ 1 = bρ 2 := by rw [bρ1, bρ2]; ring
  have e2 : AdjoinRoot.root fρ * bρ 2 = bρ 0 + bρ 1 := by rw [← powρ3, bρ2]; ring
  rw [e0, e1, e2]
  simp

theorem tρ2 : Algebra.trace ℚ (AdjoinRoot fρ) (AdjoinRoot.root fρ ^ 2) = 2 := by
  rw [traceρ_eq]
  have e0 : AdjoinRoot.root fρ ^ 2 * bρ 0 = bρ 2 := by rw [bρ0, bρ2]; ring
  have e1 : AdjoinRoot.root fρ ^ 2 * bρ 1 = bρ 0 + bρ 1 := by rw [← powρ3, bρ1]; ring
  have e2 : AdjoinRoot.root fρ ^ 2 * bρ 2 = bρ 1 + bρ 2 := by rw [← powρ4, bρ2]; ring
  rw [e0, e1, e2]
  simp
  norm_num

theorem tρ3 : Algebra.trace ℚ (AdjoinRoot fρ) (AdjoinRoot.root fρ ^ 3) = 3 := by
  rw [rρ_pow_three, map_add, tρ1, tρ0]; norm_num

theorem tρ4 : Algebra.trace ℚ (AdjoinRoot fρ) (AdjoinRoot.root fρ ^ 4) = 2 := by
  rw [rρ_pow_four, map_add, tρ2, tρ1]; norm_num

/-- The power sums of `X⁴ − X − 1`: `p₀,…,p₆ = 4, 0, 0, 3, 4, 0, 3`. -/
theorem trace_rootQ_pow (k : ℕ) (hk : k ≤ 6) :
    Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ ^ k)
      = ![4, 0, 0, 3, 4, 0, 3] (⟨k, by omega⟩ : Fin 7) := by
  have h : ∀ i : Fin 7, Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ ^ (i : ℕ))
      = ![4, 0, 0, 3, 4, 0, 3] i := by
    intro i
    fin_cases i <;> simp [tQ0, tQ1, tQ2, tQ3, tQ4, tQ5, tQ6]
  exact h ⟨k, by omega⟩

/-- The power sums of `X³ − X − 1`: `p₀,…,p₄ = 3, 0, 2, 3, 2`. -/
theorem trace_rootρ_pow (k : ℕ) (hk : k ≤ 4) :
    Algebra.trace ℚ (AdjoinRoot fρ) (AdjoinRoot.root fρ ^ k)
      = ![3, 0, 2, 3, 2] (⟨k, by omega⟩ : Fin 5) := by
  have h : ∀ i : Fin 5, Algebra.trace ℚ (AdjoinRoot fρ) (AdjoinRoot.root fρ ^ (i : ℕ))
      = ![3, 0, 2, 3, 2] i := by
    intro i
    fin_cases i <;> simp [tρ0, tρ1, tρ2, tρ3, tρ4]
  exact h ⟨k, by omega⟩

/-! ### The Gram matrices of the trace form -/

theorem traceMatrix_bQ_apply (i j : Fin 4) :
    Algebra.traceMatrix ℚ (⇑bQ) i j
      = Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ ^ ((i : ℕ) + (j : ℕ))) := by
  rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, bQ_apply, bQ_apply, ← pow_add]

theorem traceMatrix_bρ_apply (i j : Fin 3) :
    Algebra.traceMatrix ℚ (⇑bρ) i j
      = Algebra.trace ℚ (AdjoinRoot fρ) (AdjoinRoot.root fρ ^ ((i : ℕ) + (j : ℕ))) := by
  rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, bρ_apply, bρ_apply, ← pow_add]

/-- **The quartic link.** The integer matrix `M` of `PdtSignature` is the Gram matrix
of the trace form of `ℚ[X]/(X⁴ − X − 1)` in the power basis `1, r, r², r³`. -/
theorem traceMatrix_bQ : Algebra.traceMatrix ℚ (⇑bQ) = M := by
  ext i j
  rw [traceMatrix_bQ_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [M, tQ0, tQ1, tQ2, tQ3, tQ4, tQ5, tQ6]

/-- **The cubic link.** The integer matrix `Mρ` of `PdtSignatureRho` is the Gram matrix
of the trace form of `ℚ[X]/(X³ − X − 1)` in the power basis `1, r, r²`. -/
theorem traceMatrix_bρ : Algebra.traceMatrix ℚ (⇑bρ) = Mρ := by
  ext i j
  rw [traceMatrix_bρ_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [Mρ, tρ0, tρ1, tρ2, tρ3, tρ4]

/-- The same statement, phrased for the unreindexed `PowerBasis` of `AdjoinRoot fQ`. -/
theorem traceMatrix_Q (i j : Fin pbQ.dim) :
    Algebra.traceMatrix ℚ (⇑pbQ.basis) i j = M (Fin.cast pbQ_dim i) (Fin.cast pbQ_dim j) := by
  have h : Algebra.traceMatrix ℚ (⇑bQ) (finCongr pbQ_dim i) (finCongr pbQ_dim j)
      = Algebra.traceMatrix ℚ (⇑pbQ.basis) i j := by
    show Algebra.traceMatrix ℚ (⇑(pbQ.basis.reindex (finCongr pbQ_dim)))
        (finCongr pbQ_dim i) (finCongr pbQ_dim j) = _
    rw [Algebra.traceMatrix_reindex]
    simp
  rw [← h, traceMatrix_bQ]
  rfl

/-- The same statement, phrased for the unreindexed `PowerBasis` of `AdjoinRoot fρ`. -/
theorem traceMatrix_ρ (i j : Fin pbρ.dim) :
    Algebra.traceMatrix ℚ (⇑pbρ.basis) i j = Mρ (Fin.cast pbρ_dim i) (Fin.cast pbρ_dim j) := by
  have h : Algebra.traceMatrix ℚ (⇑bρ) (finCongr pbρ_dim i) (finCongr pbρ_dim j)
      = Algebra.traceMatrix ℚ (⇑pbρ.basis) i j := by
    show Algebra.traceMatrix ℚ (⇑(pbρ.basis.reindex (finCongr pbρ_dim)))
        (finCongr pbρ_dim i) (finCongr pbρ_dim j) = _
    rw [Algebra.traceMatrix_reindex]
    simp
  rw [← h, traceMatrix_bρ]
  rfl

/-! ### The power-basis discriminants -/

/-- **The discriminant of the power basis of `ℚ[X]/(X⁴ − X − 1)` is `−283`.** -/
theorem discr_Q : Algebra.discr ℚ pbQ.basis = -283 := by
  have h : Algebra.discr ℚ (⇑bQ) = Algebra.discr ℚ (⇑pbQ.basis) := by
    show Algebra.discr ℚ (⇑(pbQ.basis.reindex (finCongr pbQ_dim))) = _
    rw [Basis.coe_reindex]
    exact Algebra.discr_reindex ℚ pbQ.basis (finCongr pbQ_dim)
  rw [← h, Algebra.discr_def, traceMatrix_bQ, det_M]

/-- **The discriminant of the power basis of `ℚ[X]/(X³ − X − 1)` is `−23`.** -/
theorem discr_ρ : Algebra.discr ℚ pbρ.basis = -23 := by
  have h : Algebra.discr ℚ (⇑bρ) = Algebra.discr ℚ (⇑pbρ.basis) := by
    show Algebra.discr ℚ (⇑(pbρ.basis.reindex (finCongr pbρ_dim))) = _
    rw [Basis.coe_reindex]
    exact Algebra.discr_reindex ℚ pbρ.basis (finCongr pbρ_dim)
  rw [← h, Algebra.discr_def, traceMatrix_bρ, detMρ]

end HermiteCompositum.Port014

-- ===== PdtTraceSignature (ported from PALOMAR-2026-09-02-000014) =====

/-!
# Sylvester signatures of the trace forms of `ℚ[x]/(x⁴ − x − 1)` and `ℚ[x]/(x³ − x − 1)`

`PdtSignature` and `PdtSignatureRho` exhibit explicit rational congruences carrying the
Gram matrices `M` and `Mρ` to diagonal matrices `D = diag(4, 4, -9/4, 283/36)` and
`Dρ = diag(3, 2, -23/6)`, and `PdtTraceLink` proves that `M` and `Mρ` really are the Gram
matrices of the trace forms in the power bases.

This file upgrades those matrix statements to statements about the *quadratic form itself*,
using Mathlib's basis-free invariants `sigPos` and `sigNeg` (the maximal dimension of a
positive- resp. negative-definite subspace).  The results

* `sigPos_traceQ`, `sigNeg_traceQ` : the trace form of `ℚ[x]/(x⁴ − x − 1)` has
  signature `(3, 1)`;
* `sigPos_traceρ`, `sigNeg_traceρ` : the trace form of `ℚ[x]/(x³ − x − 1)` has
  signature `(2, 1)`

are therefore *intrinsic invariants of the field*, independent of the chosen basis and of
the chosen diagonalising congruence.  The uniqueness half of Sylvester's law of inertia is
supplied by `QuadraticForm.sigPos_of_equiv_weightedSumSquares`.
-/

namespace HermiteCompositum.Port014

open Module QuadraticMap

/-! ## The quartic side: `K = ℚ[x]/(x⁴ − x − 1)` -/

/-- The trace form `(x, y) ↦ Tr_{K/ℚ}(x y)` of `K = ℚ[x]/(x⁴ − x − 1)`, viewed as a
quadratic form `x ↦ Tr_{K/ℚ}(x²)`. -/
noncomputable def qTraceQ : QuadraticForm ℚ (AdjoinRoot fQ) :=
  LinearMap.BilinMap.toQuadraticMap (Algebra.traceForm ℚ (AdjoinRoot fQ))

theorem qTraceQ_apply (x : AdjoinRoot fQ) :
    qTraceQ x = Algebra.trace ℚ (AdjoinRoot fQ) (x * x) := by
  rw [qTraceQ, LinearMap.BilinMap.toQuadraticMap_apply, Algebra.traceForm_apply]

/-- The Gram matrix entries of the trace form in the power basis are the entries of `M`. -/
theorem traceForm_bQ (i j : Fin 4) :
    Algebra.traceForm ℚ (AdjoinRoot fQ) (bQ i) (bQ j) = M i j := by
  have h : Algebra.traceMatrix ℚ (⇑bQ) i j
      = Algebra.traceForm ℚ (AdjoinRoot fQ) (bQ i) (bQ j) := by
    rw [Algebra.traceMatrix_apply]
  rw [traceMatrix_bQ] at h
  exact h.symm

/-- The value of the trace form on a general combination of the power basis. -/
theorem qTraceQ_comb (a₀ a₁ a₂ a₃ : ℚ) :
    qTraceQ (a₀ • bQ 0 + a₁ • bQ 1 + a₂ • bQ 2 + a₃ • bQ 3)
      = 4 * a₀ * a₀ + 6 * a₀ * a₃ + 6 * a₁ * a₂ + 8 * a₁ * a₃ + 4 * a₂ * a₂ + 3 * a₃ * a₃ := by
  rw [qTraceQ, LinearMap.BilinMap.toQuadraticMap_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    traceForm_bQ, M, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  ring

/-! ### The diagonalising basis: the columns of `P` -/

/-- The basis of `K` whose transition matrix from the power basis is `P`; by
`PDT.congruence` it is orthogonal for the trace form. -/
noncomputable def cQ : Basis (Fin 4) ℚ (AdjoinRoot fQ) :=
  bQ.map (Matrix.toLinearEquiv bQ P P_isUnit)

theorem cQ_apply (i : Fin 4) : cQ i = ∑ j, P j i • bQ j := by
  show (bQ.map (Matrix.toLinearEquiv bQ P P_isUnit)) i = _
  rw [Basis.map_apply]
  simp

theorem sum_cQ (w : Fin 4 → ℚ) :
    ∑ i, w i • cQ i
      = (w 0 + (-3 / 4) * w 3) • bQ 0 + (w 2 + (16 / 9) * w 3) • bQ 1
        + (w 1 + (-3 / 4) * w 2 + (-4 / 3) * w 3) • bQ 2 + (w 3) • bQ 3 := by
  simp only [cQ_apply, Fin.sum_univ_four, P, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const]
  module

/-- The basis representation of the trace form in the basis `cQ` is the weighted sum of
squares with weights the diagonal of `D = diag(4, 4, -9/4, 283/36)`. -/
theorem basisRepr_cQ_apply (w : Fin 4 → ℚ) :
    qTraceQ.basisRepr cQ w = weightedSumSquares ℚ (fun i : Fin 4 => D i i) w := by
  rw [QuadraticMap.basisRepr_apply, sum_cQ, qTraceQ_comb, weightedSumSquares_apply]
  simp only [Fin.sum_univ_four, smul_eq_mul, D, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const]
  ring

theorem basisRepr_cQ : qTraceQ.basisRepr cQ = weightedSumSquares ℚ (fun i : Fin 4 => D i i) := by
  ext w
  exact basisRepr_cQ_apply w

/-- **The quartic trace form is equivalent to `diag(4, 4, -9/4, 283/36)`.** -/
theorem qTraceQ_equiv :
    QuadraticMap.Equivalent qTraceQ (weightedSumSquares ℚ (fun i : Fin 4 => D i i)) := by
  refine ⟨?_⟩
  rw [← basisRepr_cQ]
  exact QuadraticMap.isometryEquivBasisRepr qTraceQ cQ

/-! ### The signature -/

/-- **The trace form of `ℚ[x]/(x⁴ − x − 1)` has three positive squares.** -/
theorem sigPos_traceQ : sigPos qTraceQ = 3 := by
  rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares qTraceQ_equiv, Set.ncard_eq_three]
  refine ⟨0, 1, 3, by decide, by decide, by decide, ?_⟩
  ext i
  fin_cases i <;> norm_num [D] <;> decide

/-- **The trace form of `ℚ[x]/(x⁴ − x − 1)` has one negative square.** -/
theorem sigNeg_traceQ : sigNeg qTraceQ = 1 := by
  rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares qTraceQ_equiv, Set.ncard_eq_one]
  refine ⟨2, ?_⟩
  ext i
  fin_cases i <;> norm_num [D] <;> decide

/-- **Signature `(3, 1)` for `ℚ[x]/(x⁴ − x − 1)`, as an intrinsic invariant.** -/
theorem traceForm_signature_Q : sigPos qTraceQ = 3 ∧ sigNeg qTraceQ = 1 :=
  ⟨sigPos_traceQ, sigNeg_traceQ⟩

/-! ## The cubic side: `k = ℚ[x]/(x³ − x − 1)` -/

/-- The trace form `(x, y) ↦ Tr_{k/ℚ}(x y)` of `k = ℚ[x]/(x³ − x − 1)`, viewed as a
quadratic form `x ↦ Tr_{k/ℚ}(x²)`. -/
noncomputable def qTraceρ : QuadraticForm ℚ (AdjoinRoot fρ) :=
  LinearMap.BilinMap.toQuadraticMap (Algebra.traceForm ℚ (AdjoinRoot fρ))

theorem qTraceρ_apply (x : AdjoinRoot fρ) :
    qTraceρ x = Algebra.trace ℚ (AdjoinRoot fρ) (x * x) := by
  rw [qTraceρ, LinearMap.BilinMap.toQuadraticMap_apply, Algebra.traceForm_apply]

/-- The Gram matrix entries of the trace form in the power basis are the entries of `Mρ`. -/
theorem traceForm_bρ (i j : Fin 3) :
    Algebra.traceForm ℚ (AdjoinRoot fρ) (bρ i) (bρ j) = Mρ i j := by
  have h : Algebra.traceMatrix ℚ (⇑bρ) i j
      = Algebra.traceForm ℚ (AdjoinRoot fρ) (bρ i) (bρ j) := by
    rw [Algebra.traceMatrix_apply]
  rw [traceMatrix_bρ] at h
  exact h.symm

/-- The value of the trace form on a general combination of the power basis. -/
theorem qTraceρ_comb (a₀ a₁ a₂ : ℚ) :
    qTraceρ (a₀ • bρ 0 + a₁ • bρ 1 + a₂ • bρ 2)
      = 3 * a₀ * a₀ + 4 * a₀ * a₂ + 2 * a₁ * a₁ + 6 * a₁ * a₂ + 2 * a₂ * a₂ := by
  rw [qTraceρ, LinearMap.BilinMap.toQuadraticMap_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    traceForm_bρ, Mρ, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  ring

/-- The basis of `k` whose transition matrix from the power basis is `Pρ`; by
`PDT.congruenceρ` it is orthogonal for the trace form. -/
noncomputable def cρ : Basis (Fin 3) ℚ (AdjoinRoot fρ) :=
  bρ.map (Matrix.toLinearEquiv bρ Pρ Pρ_isUnit)

theorem cρ_apply (i : Fin 3) : cρ i = ∑ j, Pρ j i • bρ j := by
  show (bρ.map (Matrix.toLinearEquiv bρ Pρ Pρ_isUnit)) i = _
  rw [Basis.map_apply]
  simp

theorem sum_cρ (w : Fin 3 → ℚ) :
    ∑ i, w i • cρ i
      = (w 0 + (-2 / 3) * w 2) • bρ 0 + (w 1 + (-3 / 2) * w 2) • bρ 1 + (w 2) • bρ 2 := by
  simp only [cρ_apply, Fin.sum_univ_three, Pρ, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const]
  module

/-- The basis representation of the trace form in the basis `cρ` is the weighted sum of
squares with weights the diagonal of `Dρ = diag(3, 2, -23/6)`. -/
theorem basisRepr_cρ_apply (w : Fin 3 → ℚ) :
    qTraceρ.basisRepr cρ w = weightedSumSquares ℚ (fun i : Fin 3 => Dρ i i) w := by
  rw [QuadraticMap.basisRepr_apply, sum_cρ, qTraceρ_comb, weightedSumSquares_apply]
  simp only [Fin.sum_univ_three, smul_eq_mul, Dρ, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const]
  ring

theorem basisRepr_cρ : qTraceρ.basisRepr cρ = weightedSumSquares ℚ (fun i : Fin 3 => Dρ i i) := by
  ext w
  exact basisRepr_cρ_apply w

/-- **The cubic trace form is equivalent to `diag(3, 2, -23/6)`.** -/
theorem qTraceρ_equiv :
    QuadraticMap.Equivalent qTraceρ (weightedSumSquares ℚ (fun i : Fin 3 => Dρ i i)) := by
  refine ⟨?_⟩
  rw [← basisRepr_cρ]
  exact QuadraticMap.isometryEquivBasisRepr qTraceρ cρ

/-- **The trace form of `ℚ[x]/(x³ − x − 1)` has two positive squares.** -/
theorem sigPos_traceρ : sigPos qTraceρ = 2 := by
  rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares qTraceρ_equiv, Set.ncard_eq_two]
  refine ⟨0, 1, by decide, ?_⟩
  ext i
  fin_cases i <;> norm_num [Dρ]

/-- **The trace form of `ℚ[x]/(x³ − x − 1)` has one negative square.** -/
theorem sigNeg_traceρ : sigNeg qTraceρ = 1 := by
  rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares qTraceρ_equiv, Set.ncard_eq_one]
  refine ⟨2, ?_⟩
  ext i
  fin_cases i <;> norm_num [Dρ] <;> decide

/-- **Signature `(2, 1)` for `ℚ[x]/(x³ − x − 1)`, as an intrinsic invariant.** -/
theorem traceForm_signature_ρ : sigPos qTraceρ = 2 ∧ sigNeg qTraceρ = 1 :=
  ⟨sigPos_traceρ, sigNeg_traceρ⟩

end HermiteCompositum.Port014

-- ===== PdtIrreducible (ported from PALOMAR-2026-09-02-000014) =====

namespace HermiteCompositum.Port014

open Polynomial

-- `cubicZ`, `quarticZ` and the proofs that `x³ − x − 1` and `x⁴ − x − 1` are irreducible over
-- `ℚ` are in `HermiteCompositum/Defs.lean` (shared verbatim with `Challenge.lean`).

/-- The unique irreducible quadratic X²+X+1 over 𝔽₂ is irreducible. -/
lemma quad_irred_zmod2 : Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
  have hm : (X ^ 2 + X + 1 : (ZMod 2)[X]).Monic := by monicity!
  have hnd : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
  by_contra h
  rw [hm.not_irreducible_iff_exists_add_mul_eq_coeff hnd] at h
  obtain ⟨c₁, c₂, hmul, hadd⟩ := h
  have hc0 : (X ^ 2 + X + 1 : (ZMod 2)[X]).coeff 0 = 1 := by
    simp [coeff_add, coeff_X_pow, coeff_X, coeff_one]
  have hc1 : (X ^ 2 + X + 1 : (ZMod 2)[X]).coeff 1 = 1 := by
    simp [coeff_add, coeff_X_pow, coeff_X, coeff_one]
  rw [hc0] at hmul
  rw [hc1] at hadd
  revert hmul hadd
  fin_cases c₁ <;> fin_cases c₂ <;> decide

end HermiteCompositum.Port014

-- ===== from PdtTraceTensor, section Instance (ported from PALOMAR-2026-09-02-000014) =====

namespace HermiteCompositum.Port014

/-- The discriminant of the reindexed cubic power basis `bρ` is `−23`
(ported from PALOMAR-2026-09-02-000014). -/
theorem discr_bρ : Algebra.discr ℚ (⇑bρ) = -23 := by
  rw [Algebra.discr_def, traceMatrix_bρ, detMρ]

/-- The discriminant of the reindexed quartic power basis `bQ` is `−283`
(ported from PALOMAR-2026-09-02-000014). -/
theorem discr_bQ : Algebra.discr ℚ (⇑bQ) = -283 := by
  rw [Algebra.discr_def, traceMatrix_bQ, det_M]

end HermiteCompositum.Port014
