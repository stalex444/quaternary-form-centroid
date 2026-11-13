module
public import Mathlib
public import HermiteCompositum.Instance

@[expose] public section

/-!
# Definitions for the form-centroid statements

One definition, with the lemmas that pin it down:

* `traceGram F` — the symmetric `4 × 4` matrix with rows `(4, 0, 0, 3)`, `(0, 0, 3, 4)`,
  `(0, 3, 4, 0)`, `(3, 4, 0, 3)`, with entries in a field `F`.
* `traceGram_apply`, `traceGram_isSymm`, `traceGram_det` (determinant `-283`), `traceGram_map`
  (compatibility with a ring homomorphism), `traceGram_rat_map_real`.
* `traceGram_eq_trace`: over `ℚ`, the entry `(i, j)` is the trace over `ℚ` of `gen₄ ^ (i + j)`,
  where `gen₄` is the generator of the field `S₄ = ℚ⟮Q⟯` of `HermiteCompositum.Instance`
  (`Q` a root of `x⁴ - x - 1`); `traceGram_eq_traceForm`: `traceGram ℚ` is the Gram matrix of the
  trace form of `S₄` on `1, gen₄, gen₄², gen₄³`.

This file contains no statement about Lie algebras.
-/

set_option autoImplicit false

namespace LorentzLie

open HermiteCompositum.Instance

/-- The symmetric `4 × 4` matrix with rows `(4, 0, 0, 3)`, `(0, 0, 3, 4)`, `(0, 3, 4, 0)`,
`(3, 4, 0, 3)`, with entries in a field `F`. Its `(i, j)` entry is the `(i + j)`-th entry of the
list `4, 0, 0, 3, 4, 0, 3` (`traceGram_apply`). -/
def traceGram (F : Type*) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![4, 0, 0, 3; 0, 0, 3, 4; 0, 3, 4, 0; 3, 4, 0, 3]

/-- The `(i, j)` entry of `traceGram F` is the entry with index `i + j` of the list
`4, 0, 0, 3, 4, 0, 3`. -/
theorem traceGram_apply (F : Type*) [Field F] (i j : Fin 4) :
    traceGram F i j = (![4, 0, 0, 3, 4, 0, 3] : Fin 7 → F) ⟨(i : ℕ) + (j : ℕ), by omega⟩ := by
  fin_cases i <;> fin_cases j <;> rfl

/-- `traceGram F` is a symmetric matrix. -/
theorem traceGram_isSymm (F : Type*) [Field F] : (traceGram F).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The determinant of `traceGram F` is `-283`, over every field `F`. -/
theorem traceGram_det (F : Type*) [Field F] : (traceGram F).det = -283 := by
  simp [traceGram, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove]
  norm_num

/-- A ring homomorphism `f : F →+* F'` of fields maps `traceGram F` entrywise to `traceGram F'`. -/
theorem traceGram_map {F F' : Type*} [Field F] [Field F'] (f : F →+* F') :
    (traceGram F).map f = traceGram F' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [traceGram, map_ofNat]

/-- The entrywise image of `traceGram ℚ` under `ℚ → ℝ` is `traceGram ℝ`. -/
theorem traceGram_rat_map_real : (traceGram ℚ).map (algebraMap ℚ ℝ) = traceGram ℝ :=
  traceGram_map (algebraMap ℚ ℝ)

/-- Over `ℚ`, the `(i, j)` entry of `traceGram ℚ` is the trace over `ℚ` of `gen₄ ^ (i + j)` in the
field `S₄ = ℚ⟮Q⟯` (`Q` a root of `x⁴ - x - 1`, `gen₄` its generator). -/
theorem traceGram_eq_trace (i j : Fin 4) :
    traceGram ℚ i j = Algebra.trace ℚ S₄ (gen₄ ^ ((i : ℕ) + (j : ℕ))) := by
  rw [trace_gen₄_pow _ (by omega), traceGram_apply]

/-- Over `ℚ`, the `(i, j)` entry of `traceGram ℚ` is the value of the trace form of `S₄ = ℚ⟮Q⟯`
over `ℚ` on the pair `(gen₄ ^ i, gen₄ ^ j)`: `traceGram ℚ` is the Gram matrix of the trace form on
`1, gen₄, gen₄², gen₄³`. -/
theorem traceGram_eq_traceForm (i j : Fin 4) :
    traceGram ℚ i j = Algebra.traceForm ℚ S₄ (gen₄ ^ (i : ℕ)) (gen₄ ^ (j : ℕ)) := by
  rw [traceGram_eq_trace, Algebra.traceForm_apply, pow_add]

end LorentzLie
