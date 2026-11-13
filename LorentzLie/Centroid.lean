module
public import Mathlib
public import LorentzLie.Defs
public import GravityScreening.SignedLieGeneration

@[expose] public section

/-!
# Bracket-commuting endomorphisms of the `η`-skew matrices

For a field `K` in which `2 ≠ 0`, a finite index type `ι` and `η : ι → K` with nonzero entries,
this file determines the linear endomorphisms `R` of `etaSkew η` with `R ⁅X, Y⁆ = ⁅X, R Y⁆`:

* `centroid_scalar_of_two_ne_zero`, `centroid_scalar` — if `Fintype.card ι ≠ 4`, then `R = c • id`;
* `centroid_scalar_so'`, `centroid_scalar_so'_four_two` — the same on Mathlib's `so' p q ℝ`, and at
  `so' (Fin 4) (Fin 2) ℝ` with `LinearMap.det R = c ^ 15`;
* `hodge_centroid_field`, `hodge_centroid_real` — for `ι = Fin 4` the operator `hodge η` is
  bracket-commuting, squares to `(∏ i, η i) • id`, and every such `R` is uniquely
  `a • id + b • hodge η`;
* `centroid_control_card_four` — `hodge η` is not a scalar.

The argument: `R (gen η a b)` commutes with every element that commutes with `gen η a b`, which
forces its entries off the positions `(a, b)`, `(b, a)` to vanish when `Fintype.card ι ≠ 4`; the
elements on which two bracket-commuting maps agree are stable under every `⁅X, ·⁆`, and one
generator generates everything under these operations.
-/

set_option autoImplicit false

attribute [local instance] LieRing.ofAssociativeRing

namespace LorentzLie

open Matrix

/-! ### Generators: brackets, expansion, generation -/

section General

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- `gen η i i = 0`. -/
theorem gen_self (η : ι → K) (i : ι) : gen η i i = 0 := by
  apply Subtype.ext
  simp [gen_coe]

/-- `gen η j i = -gen η i j`. -/
theorem gen_swap (η : ι → K) (i j : ι) : gen η j i = -gen η i j := by
  apply Subtype.ext
  simp [gen_coe]

/-- `⁅gen η i j, gen η j k⁆ = η j • gen η i k` for distinct `i`, `j`, `k`. -/
theorem lie_gen_gen (η : ι → K) {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅gen η i j, gen η j k⁆ = η j • gen η i k := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket]
  simp [gen_coe, Ring.lie_def, mul_sub, sub_mul, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, hij, hik, hjk, hij.symm, hik.symm, hjk.symm, smul_sub,
    Matrix.smul_single, mul_comm]

/-- Generators on disjoint pairs of indices commute. -/
theorem lie_gen_gen_of_disjoint (η : ι → K) {k l a b : ι} (hka : k ≠ a) (hkb : k ≠ b)
    (hla : l ≠ a) (hlb : l ≠ b) : ⁅gen η k l, gen η a b⁆ = 0 := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket]
  simp [gen_coe, Ring.lie_def, mul_sub, sub_mul, Matrix.single_mul_single_of_ne, hka, hkb, hla,
    hlb, hka.symm, hkb.symm, hla.symm, hlb.symm]

/-- The diagonal of an `η`-skew matrix vanishes. -/
theorem etaSkew_apply_self (h2 : (2 : K) ≠ 0) (η : ι → K) (hη : ∀ i, η i ≠ 0) (X : etaSkew η)
    (i : ι) : (X : Matrix ι ι K) i i = 0 := by
  have h := (mem_etaSkew_iff η X.1).mp X.2 i i
  have h3 : (2 * η i) * (X : Matrix ι ι K) i i = 0 := by linear_combination h
  exact (mul_eq_zero.mp h3).resolve_left (mul_ne_zero h2 (hη i))

/-- Every `η`-skew matrix is a combination of the generators. -/
theorem eq_sum_gen (h2 : (2 : K) ≠ 0) (η : ι → K) (hη : ∀ i, η i ≠ 0) (X : etaSkew η) :
    X = ∑ i, ∑ j, ((X : Matrix ι ι K) i j / (2 * η j)) • gen η i j := by
  have hX := (mem_etaSkew_iff η X.1).mp X.2
  have key : ∀ i j, ((X : Matrix ι ι K) i j / (2 * η j)) • (gen η i j : Matrix ι ι K) =
      Matrix.single i j ((2 : K)⁻¹ * (X : Matrix ι ι K) i j) +
        Matrix.single j i ((2 : K)⁻¹ * (X : Matrix ι ι K) j i) := by
    intro i j
    have hj := hη j
    have e1 : (X : Matrix ι ι K) i j / (2 * η j) * η j = (2 : K)⁻¹ * (X : Matrix ι ι K) i j := by
      field_simp
    have e2 : (X : Matrix ι ι K) i j / (2 * η j) * η i =
        -((2 : K)⁻¹ * (X : Matrix ι ι K) j i) := by
      field_simp
      linear_combination hX i j
    rw [gen_coe, smul_sub, Matrix.smul_single, Matrix.smul_single, smul_eq_mul, smul_eq_mul, e1,
      e2, ← Matrix.single_neg, sub_neg_eq_add]
  have hS : ∑ i, ∑ j, Matrix.single i j ((2 : K)⁻¹ * (X : Matrix ι ι K) i j) =
      (2 : K)⁻¹ • (X : Matrix ι ι K) := by
    conv_rhs => rw [Matrix.matrix_eq_sum_single (X : Matrix ι ι K)]
    simp only [Finset.smul_sum, Matrix.smul_single, smul_eq_mul]
  have hhalf : (2 : K)⁻¹ + 2⁻¹ = 1 := by rw [← two_mul, mul_inv_cancel₀ h2]
  apply Subtype.ext
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, key, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => Matrix.single j i ((2 : K)⁻¹ * (X : Matrix ι ι K) j i)),
    hS, ← add_smul, hhalf, one_smul]

/-- A linear map on `etaSkew η` that vanishes on every generator is zero. -/
theorem linearMap_eq_zero_of_gen (h2 : (2 : K) ≠ 0) (η : ι → K) (hη : ∀ i, η i ≠ 0)
    (R : etaSkew η →ₗ[K] etaSkew η) (h : ∀ i j, R (gen η i j) = 0) : R = 0 := by
  apply LinearMap.ext
  intro X
  have hX := eq_sum_gen h2 η hη X
  rw [hX]
  simp only [map_sum, map_smul, h, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]

/-- A submodule of `etaSkew η` stable under every `⁅X, ·⁆` that contains one generator `gen η a b`
with `a ≠ b` contains every generator. -/
theorem gen_mem_of_lie_closed (η : ι → K) (hη : ∀ i, η i ≠ 0) (S : Submodule K (etaSkew η))
    (hS : ∀ X : etaSkew η, ∀ Y ∈ S, ⁅X, Y⁆ ∈ S) {a b : ι} (hab : a ≠ b)
    (h : gen η a b ∈ S) : ∀ i j, gen η i j ∈ S := by
  have hrow : ∀ k, gen η a k ∈ S := by
    intro k
    by_cases hka : k = a
    · rw [hka, gen_self]; exact S.zero_mem
    by_cases hkb : k = b
    · rw [hkb]; exact h
    have h1 : gen η b a ∈ S := by rw [gen_swap]; exact S.neg_mem h
    have h2 := hS (gen η k b) _ h1
    rw [lie_gen_gen η hkb hka (Ne.symm hab)] at h2
    have h3 := S.smul_mem (η b)⁻¹ h2
    rw [smul_smul, inv_mul_cancel₀ (hη b), one_smul] at h3
    rw [gen_swap]; exact S.neg_mem h3
  intro i j
  by_cases hia : i = a
  · rw [hia]; exact hrow j
  by_cases hij : i = j
  · rw [hij, gen_self]; exact S.zero_mem
  by_cases hja : j = a
  · rw [hja, gen_swap]; exact S.neg_mem (hrow i)
  have h2 := hS (gen η i a) _ (hrow j)
  rw [lie_gen_gen η hia hij (Ne.symm hja)] at h2
  have h3 := S.smul_mem (η a)⁻¹ h2
  rwa [smul_smul, inv_mul_cancel₀ (hη a), one_smul] at h3

/-- A bracket-commuting linear map that vanishes on one generator `gen η a b`, `a ≠ b`, is zero. -/
theorem eq_zero_of_apply_gen_eq_zero (h2 : (2 : K) ≠ 0) (η : ι → K) (hη : ∀ i, η i ≠ 0)
    (R : etaSkew η →ₗ[K] etaSkew η) (hR : ∀ X Y : etaSkew η, R ⁅X, Y⁆ = ⁅X, R Y⁆) {a b : ι}
    (hab : a ≠ b) (h : R (gen η a b) = 0) : R = 0 := by
  have hS : ∀ X : etaSkew η, ∀ Y ∈ LinearMap.ker R, ⁅X, Y⁆ ∈ LinearMap.ker R := by
    intro X Y hY
    rw [LinearMap.mem_ker] at hY ⊢
    rw [hR, hY, lie_zero]
  have hall := gen_mem_of_lie_closed η hη (LinearMap.ker R) hS hab (LinearMap.mem_ker.mpr h)
  exact linearMap_eq_zero_of_gen h2 η hη R fun i j => LinearMap.mem_ker.mp (hall i j)

/-- If a matrix `Z` commutes with `gen η a b`, `a ≠ b`, then the rows `a` and `b` of `Z` vanish
outside the columns `a`, `b`. -/
theorem apply_eq_zero_of_lie_gen (η : ι → K) (hη : ∀ i, η i ≠ 0) {a b : ι} (hab : a ≠ b)
    (Z : Matrix ι ι K) (h : ⁅(gen η a b : Matrix ι ι K), Z⁆ = 0) {m : ι} (hma : m ≠ a)
    (hmb : m ≠ b) : Z a m = 0 ∧ Z b m = 0 := by
  rw [Ring.lie_def, gen_coe, sub_mul, mul_sub] at h
  constructor
  · have h1 := congrFun (congrFun h b) m
    simp only [Matrix.sub_apply, Matrix.zero_apply] at h1
    rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hab.symm, Matrix.single_mul_apply_same,
      Matrix.mul_single_apply_of_ne _ _ _ _ _ hmb, Matrix.mul_single_apply_of_ne _ _ _ _ _ hma]
      at h1
    have h3 : η a * Z a m = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp h3).resolve_left (hη a)
  · have h1 := congrFun (congrFun h a) m
    simp only [Matrix.sub_apply, Matrix.zero_apply] at h1
    rw [Matrix.single_mul_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hab,
      Matrix.mul_single_apply_of_ne _ _ _ _ _ hmb, Matrix.mul_single_apply_of_ne _ _ _ _ _ hma]
      at h1
    have h3 : η b * Z b m = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h3).resolve_left (hη b)

/-- For a bracket-commuting `R` and `a ≠ b`, the matrix `R (gen η a b)` has rows `a` and `b`
supported in the columns `a`, `b`, and columns `a` and `b` supported in the rows `a`, `b`. -/
theorem apply_gen_apply_eq_zero (η : ι → K) (hη : ∀ i, η i ≠ 0)
    (R : etaSkew η →ₗ[K] etaSkew η) (hR : ∀ X Y : etaSkew η, R ⁅X, Y⁆ = ⁅X, R Y⁆) {a b : ι}
    (hab : a ≠ b) {m : ι} (hma : m ≠ a) (hmb : m ≠ b) :
    (R (gen η a b) : Matrix ι ι K) a m = 0 ∧ (R (gen η a b) : Matrix ι ι K) b m = 0 ∧
      (R (gen η a b) : Matrix ι ι K) m a = 0 ∧ (R (gen η a b) : Matrix ι ι K) m b = 0 := by
  have hY := (mem_etaSkew_iff η (R (gen η a b)).1).mp (R (gen η a b)).2
  have h0 : ⁅(gen η a b : Matrix ι ι K), (R (gen η a b) : Matrix ι ι K)⁆ = 0 := by
    rw [← LieSubalgebra.coe_bracket, ← hR, lie_self, map_zero]
    rfl
  obtain ⟨h1, h2⟩ := apply_eq_zero_of_lie_gen η hη hab _ h0 hma hmb
  refine ⟨h1, h2, ?_, ?_⟩
  · have h3 := hY a m
    rw [h1, mul_zero, neg_zero] at h3
    exact (mul_eq_zero.mp h3).resolve_right (hη m)
  · have h3 := hY b m
    rw [h2, mul_zero, neg_zero] at h3
    exact (mul_eq_zero.mp h3).resolve_right (hη m)

/-- When `Fintype.card ι ≠ 4`, a bracket-commuting `R` sends each generator `gen η a b`, `a ≠ b`,
to a multiple of itself. -/
theorem apply_gen_eq_smul (h2 : (2 : K) ≠ 0) (hι : Fintype.card ι ≠ 4) (η : ι → K)
    (hη : ∀ i, η i ≠ 0) (R : etaSkew η →ₗ[K] etaSkew η)
    (hR : ∀ X Y : etaSkew η, R ⁅X, Y⁆ = ⁅X, R Y⁆) {a b : ι} (hab : a ≠ b) :
    R (gen η a b) = ((R (gen η a b) : Matrix ι ι K) a b / η b) • gen η a b := by
  have hY := (mem_etaSkew_iff η (R (gen η a b)).1).mp (R (gen η a b)).2
  have hA : ∀ m, m ≠ a → m ≠ b → _ := fun m hma hmb =>
    apply_gen_apply_eq_zero η hη R hR hab hma hmb
  have hB : ∀ l m, l ≠ a → l ≠ b → m ≠ a → m ≠ b → l ≠ m →
      (R (gen η a b) : Matrix ι ι K) l m = 0 := by
    intro l m hla hlb hma hmb hlm
    have hex : ∃ k, k ≠ a ∧ k ≠ b ∧ k ≠ l ∧ k ≠ m := by
      by_contra hcon
      push Not at hcon
      apply hι
      have hs : ({a, b, l, m} : Finset ι).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [hab, Ne.symm hla, Ne.symm hma]),
          Finset.card_insert_of_notMem (by simp [Ne.symm hlb, Ne.symm hmb]),
          Finset.card_insert_of_notMem (by simp [hlm]), Finset.card_singleton]
      have hu : (Finset.univ : Finset ι) = {a, b, l, m} := by
        symm
        apply Finset.eq_univ_of_forall
        intro k
        by_contra hk
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        exact hk.2.2.2 (hcon k hk.1 hk.2.1 hk.2.2.1)
      rw [← Finset.card_univ, hu, hs]
    obtain ⟨k, hka, hkb, hkl, hkm⟩ := hex
    have h1 : ⁅(gen η k l : Matrix ι ι K), (R (gen η a b) : Matrix ι ι K)⁆ = 0 := by
      rw [← LieSubalgebra.coe_bracket, ← hR, lie_gen_gen_of_disjoint η hka hkb hla hlb, map_zero]
      rfl
    exact (apply_eq_zero_of_lie_gen η hη hkl _ h1 (Ne.symm hkm) (Ne.symm hlm)).2
  have hd := etaSkew_apply_self h2 η hη (R (gen η a b))
  apply Subtype.ext
  ext x y
  simp only [SetLike.val_smul, gen_coe, Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply,
    smul_eq_mul]
  have hb := hη b
  by_cases hxa : x = a
  · by_cases hyb : y = b
    · rw [hxa, hyb]
      simp [hab, div_mul_cancel₀ _ hb]
    · by_cases hya : y = a
      · rw [hxa, hya, hd a]
        simp [Ne.symm hab]
      · rw [hxa, (hA y hya hyb).1]
        simp [Ne.symm hyb, Ne.symm hya, Ne.symm hab]
  · by_cases hxb : x = b
    · by_cases hya : y = a
      · rw [hxb, hya]
        simp only [hab, Ne.symm hab, and_self, ite_false, ite_true, zero_sub]
        have h3 := hY a b
        field_simp
        linear_combination h3
      · by_cases hyb : y = b
        · rw [hxb, hyb, hd b]
          simp [hab]
        · rw [hxb, (hA y hya hyb).2.1]
          simp [Ne.symm hyb, Ne.symm hya, hab]
    · by_cases hya : y = a
      · rw [hya, (hA x hxa hxb).2.2.1]
        simp [Ne.symm hxa, Ne.symm hxb]
      · by_cases hyb : y = b
        · rw [hyb, (hA x hxa hxb).2.2.2]
          simp [Ne.symm hxa, Ne.symm hxb]
        · by_cases hxy : x = y
          · rw [← hxy, hd x]
            simp [Ne.symm hxa, Ne.symm hxb]
          · rw [hB x y hxa hxb hya hyb hxy]
            simp [Ne.symm hxa, Ne.symm hxb]

/-- Subtracting a scalar from a bracket-commuting map leaves a bracket-commuting map. -/
theorem sub_smul_id_comm (η : ι → K) (R : etaSkew η →ₗ[K] etaSkew η)
    (hR : ∀ X Y : etaSkew η, R ⁅X, Y⁆ = ⁅X, R Y⁆) (c : K) (X Y : etaSkew η) :
    (R - c • (LinearMap.id : etaSkew η →ₗ[K] etaSkew η)) ⁅X, Y⁆ =
      ⁅X, (R - c • (LinearMap.id : etaSkew η →ₗ[K] etaSkew η)) Y⁆ := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hR, lie_sub, lie_smul]

/-- **The scalar theorem over a field in which `2 ≠ 0`.** If `Fintype.card ι ≠ 4` and `η` has
nonzero entries, every bracket-commuting linear endomorphism of `etaSkew η` is `c • id`. -/
theorem centroid_scalar_of_two_ne_zero (h2 : (2 : K) ≠ 0) (hι : Fintype.card ι ≠ 4) (η : ι → K)
    (hη : ∀ i, η i ≠ 0) (R : etaSkew η →ₗ[K] etaSkew η)
    (hR : ∀ X Y : etaSkew η, R ⁅X, Y⁆ = ⁅X, R Y⁆) : ∃ c : K, R = c • LinearMap.id := by
  by_cases hex : ∃ a b : ι, a ≠ b
  · obtain ⟨a, b, hab⟩ := hex
    refine ⟨(R (gen η a b) : Matrix ι ι K) a b / η b, ?_⟩
    have h0 : (R - ((R (gen η a b) : Matrix ι ι K) a b / η b) •
        (LinearMap.id : etaSkew η →ₗ[K] etaSkew η)) (gen η a b) = 0 := by
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
      exact apply_gen_eq_smul h2 hι η hη R hR hab
    exact sub_eq_zero.mp (eq_zero_of_apply_gen_eq_zero h2 η hη _ (sub_smul_id_comm η R hR _) hab h0)
  · push Not at hex
    refine ⟨0, ?_⟩
    rw [zero_smul]
    apply linearMap_eq_zero_of_gen h2 η hη
    intro i j
    rw [hex i j, gen_self, map_zero]

end General

/-- **L5.** Let `ι` be a finite index type whose cardinality is not `4`, let `η : ι → ℝ` have all
entries nonzero, and let `R` be a real-linear endomorphism of the Lie algebra of
`diagonal η`-skew matrices with `R ⁅X, Y⁆ = ⁅X, R Y⁆` for all `X`, `Y`. Then there is a real `c`
with `R = c • id`. -/
theorem centroid_scalar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι ≠ 4) (η : ι → ℝ) (hη : ∀ i, η i ≠ 0)
    (R : skewAdjointMatricesLieSubalgebra (Matrix.diagonal η) →ₗ[ℝ]
         skewAdjointMatricesLieSubalgebra (Matrix.diagonal η))
    (hR : ∀ X Y : skewAdjointMatricesLieSubalgebra (Matrix.diagonal η), R ⁅X, Y⁆ = ⁅X, R Y⁆) :
    ∃ c : ℝ, R = c • LinearMap.id := by
  exact centroid_scalar_of_two_ne_zero two_ne_zero hι η hη R hR

/-- **L5, on Mathlib's `so' p q ℝ`.** Let `p`, `q` be finite types with
`card p + card q ≠ 4`, and let `R` be a real-linear endomorphism of `so' p q ℝ` with
`R ⁅X, Y⁆ = ⁅X, R Y⁆` for all `X`, `Y`. Then there is a real `c` with `R = c • id`. -/
theorem centroid_scalar_so' {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (h : Fintype.card p + Fintype.card q ≠ 4)
    (R : LieAlgebra.Orthogonal.so' p q ℝ →ₗ[ℝ] LieAlgebra.Orthogonal.so' p q ℝ)
    (hR : ∀ X Y : LieAlgebra.Orthogonal.so' p q ℝ, R ⁅X, Y⁆ = ⁅X, R Y⁆) :
    ∃ c : ℝ, R = c • LinearMap.id := by
  exact centroid_scalar (ι := p ⊕ q) (by simpa using h) (Sum.elim (fun _ => 1) fun _ => -1)
    (by rintro (i | i) <;> simp) R hR

/-! ### Dimension four: the Hodge operator -/

section Four

variable {K : Type*} [Field K]

/-- The matrix `S * diagonal η` for the antisymmetric `4 × 4` matrix `S` with the six given
entries above the diagonal. Every `η`-skew `4 × 4` matrix has this form
(`etaSkew_eq_skewMat4`). -/
def skewMat4 (η : Fin 4 → K) (s01 s02 s03 s12 s13 s23 : K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, s01 * η 1, s02 * η 2, s03 * η 3;
     -(s01 * η 0), 0, s12 * η 2, s13 * η 3;
     -(s02 * η 0), -(s12 * η 1), 0, s23 * η 3;
     -(s03 * η 0), -(s13 * η 1), -(s23 * η 2), 0]

/-- Every `η`-skew `4 × 4` matrix is the matrix `skewMat4 η` of its six entries above the diagonal,
each divided by the entry of `η` at its column. -/
theorem etaSkew_eq_skewMat4 (h2 : (2 : K) ≠ 0) (η : Fin 4 → K) (hη : ∀ i, η i ≠ 0)
    (X : etaSkew η) :
    (X : Matrix (Fin 4) (Fin 4) K) =
      skewMat4 η ((X : Matrix (Fin 4) (Fin 4) K) 0 1 / η 1)
        ((X : Matrix (Fin 4) (Fin 4) K) 0 2 / η 2) ((X : Matrix (Fin 4) (Fin 4) K) 0 3 / η 3)
        ((X : Matrix (Fin 4) (Fin 4) K) 1 2 / η 2) ((X : Matrix (Fin 4) (Fin 4) K) 1 3 / η 3)
        ((X : Matrix (Fin 4) (Fin 4) K) 2 3 / η 3) := by
  have hX := (mem_etaSkew_iff η X.1).mp X.2
  have hd := etaSkew_apply_self h2 η hη X
  have up : ∀ i j, (X : Matrix (Fin 4) (Fin 4) K) i j =
      (X : Matrix (Fin 4) (Fin 4) K) i j / η j * η j := fun i j =>
    (div_mul_cancel₀ _ (hη j)).symm
  have low : ∀ i j, (X : Matrix (Fin 4) (Fin 4) K) j i =
      -((X : Matrix (Fin 4) (Fin 4) K) i j / η j * η i) := by
    intro i j
    rw [eq_div_of_mul_eq (hη j) (hX i j)]
    ring
  ext i j
  fin_cases i <;> fin_cases j
  · exact hd 0
  · exact up 0 1
  · exact up 0 2
  · exact up 0 3
  · exact low 0 1
  · exact hd 1
  · exact up 1 2
  · exact up 1 3
  · exact low 0 2
  · exact low 1 2
  · exact hd 2
  · exact up 2 3
  · exact low 0 3
  · exact low 1 3
  · exact low 2 3
  · exact hd 3

/-- The closed-form Hodge operator on the matrices `skewMat4`. -/
theorem hodgeMat_skewMat4 (η : Fin 4 → K) (s01 s02 s03 s12 s13 s23 : K) :
    hodgeMat η (skewMat4 η s01 s02 s03 s12 s13 s23) =
      skewMat4 η (η 2 * η 3 * s23) (-(η 1 * η 3 * s13)) (η 1 * η 2 * s12) (η 0 * η 3 * s03)
        (-(η 0 * η 2 * s02)) (η 0 * η 1 * s01) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hodgeMat, star0, skewMat4, Matrix.mul_apply, Matrix.diagonal_apply,
      -mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> ring1

/-- The bracket of two matrices `skewMat4` is a matrix `skewMat4`. -/
theorem lie_skewMat4 (η : Fin 4 → K) (s01 s02 s03 s12 s13 s23 t01 t02 t03 t12 t13 t23 : K) :
    ⁅skewMat4 η s01 s02 s03 s12 s13 s23, skewMat4 η t01 t02 t03 t12 t13 t23⁆ =
      skewMat4 η
        (η 2 * (s12 * t02 - s02 * t12) + η 3 * (s13 * t03 - s03 * t13))
        (η 1 * (s01 * t12 - s12 * t01) + η 3 * (s23 * t03 - s03 * t23))
        (η 1 * (s01 * t13 - s13 * t01) + η 2 * (s02 * t23 - s23 * t02))
        (η 0 * (s02 * t01 - s01 * t02) + η 3 * (s23 * t13 - s13 * t23))
        (η 0 * (s03 * t01 - s01 * t03) + η 2 * (s12 * t23 - s23 * t12))
        (η 0 * (s03 * t02 - s02 * t03) + η 1 * (s13 * t12 - s12 * t13)) := by
  rw [Ring.lie_def]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skewMat4, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> ring1

/-- Bracket-commutation of the closed-form Hodge operator on the matrices `skewMat4`: a polynomial
identity in the twelve entries and `η`. -/
theorem hodgeMat_lie_skewMat4 (η : Fin 4 → K)
    (s01 s02 s03 s12 s13 s23 t01 t02 t03 t12 t13 t23 : K) :
    hodgeMat η ⁅skewMat4 η s01 s02 s03 s12 s13 s23, skewMat4 η t01 t02 t03 t12 t13 t23⁆ =
      ⁅skewMat4 η s01 s02 s03 s12 s13 s23,
        hodgeMat η (skewMat4 η t01 t02 t03 t12 t13 t23)⁆ := by
  rw [hodgeMat_skewMat4, lie_skewMat4, lie_skewMat4, hodgeMat_skewMat4]
  congr 1 <;> ring1

/-- Part (i): `hodge η` is bracket-commuting. -/
theorem hodge_lie (h2 : (2 : K) ≠ 0) (η : Fin 4 → K) (hη : ∀ i, η i ≠ 0) (X Y : etaSkew η) :
    hodge η ⁅X, Y⁆ = ⁅X, hodge η Y⁆ := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket, hodge_coe]
  rw [etaSkew_eq_skewMat4 h2 η hη X, etaSkew_eq_skewMat4 h2 η hη Y]
  exact hodgeMat_lie_skewMat4 η _ _ _ _ _ _ _ _ _ _ _ _

/-- Part (ii): `hodge η` squares to `(∏ i, η i) • id`. -/
theorem hodge_hodge (h2 : (2 : K) ≠ 0) (η : Fin 4 → K) (hη : ∀ i, η i ≠ 0) (X : etaSkew η) :
    hodge η (hodge η X) = (∏ i, η i) • X := by
  apply Subtype.ext
  rw [hodge_coe, hodge_coe, SetLike.val_smul, etaSkew_eq_skewMat4 h2 η hη X, hodgeMat_skewMat4,
    hodgeMat_skewMat4, Fin.prod_univ_four]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewMat4] <;> ring

/-- The generator `gen η 0 1` as a matrix `skewMat4`. -/
theorem gen_zero_one_eq (η : Fin 4 → K) :
    (gen η 0 1 : Matrix (Fin 4) (Fin 4) K) = skewMat4 η 1 0 0 0 0 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewMat4, gen_coe]

/-- `id` and `hodge η` are linearly independent. -/
theorem smul_id_add_smul_hodge_eq_zero (η : Fin 4 → K) (hη : ∀ i, η i ≠ 0) (a b : K)
    (h : a • (LinearMap.id : etaSkew η →ₗ[K] etaSkew η) + b • hodge η = 0) : a = 0 ∧ b = 0 := by
  have h1 : a • (gen η 0 1 : Matrix (Fin 4) (Fin 4) K) +
      b • hodgeMat η (gen η 0 1 : Matrix (Fin 4) (Fin 4) K) = 0 :=
    congrArg Subtype.val (LinearMap.congr_fun h (gen η 0 1))
  rw [gen_zero_one_eq, hodgeMat_skewMat4] at h1
  have h01 : a * η 1 = 0 := by simpa [skewMat4] using congrFun (congrFun h1 0) 1
  have h23 : b * (η 0 * η 1 * η 3) = 0 := by simpa [skewMat4] using congrFun (congrFun h1 2) 3
  exact ⟨(mul_eq_zero.mp h01).resolve_right (hη 1),
    (mul_eq_zero.mp h23).resolve_right (mul_ne_zero (mul_ne_zero (hη 0) (hη 1)) (hη 3))⟩

/-- A matrix `skewMat4` supported on the positions `(0, 1)` and `(2, 3)` is a combination of
`gen η 0 1` and its image under the closed-form Hodge operator. -/
theorem skewMat4_eq_comb (η : Fin 4 → K) (hη : ∀ i, η i ≠ 0) (y01 y23 : K) :
    skewMat4 η (y01 / η 1) 0 0 0 0 (y23 / η 3) =
      (y01 / η 1) • skewMat4 η 1 0 0 0 0 0 +
        (y23 / (η 0 * η 1 * η 3)) • hodgeMat η (skewMat4 η 1 0 0 0 0 0) := by
  have h0 := hη 0
  have h1 := hη 1
  have h3 := hη 3
  rw [hodgeMat_skewMat4]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewMat4] <;> field_simp

/-- Part (iii), existence, with the coefficients read off `R (gen η 0 1)`. -/
theorem eq_smul_id_add_smul_hodge (h2 : (2 : K) ≠ 0) (η : Fin 4 → K) (hη : ∀ i, η i ≠ 0)
    (R : etaSkew η →ₗ[K] etaSkew η) (hR : ∀ X Y : etaSkew η, R ⁅X, Y⁆ = ⁅X, R Y⁆) :
    R = ((R (gen η 0 1) : Matrix (Fin 4) (Fin 4) K) 0 1 / η 1) • LinearMap.id +
      ((R (gen η 0 1) : Matrix (Fin 4) (Fin 4) K) 2 3 / (η 0 * η 1 * η 3)) • hodge η := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  obtain ⟨h02, h12, -, -⟩ :=
    apply_gen_apply_eq_zero η hη R hR h01 (m := 2) (by decide) (by decide)
  obtain ⟨h03, h13, -, -⟩ :=
    apply_gen_apply_eq_zero η hη R hR h01 (m := 3) (by decide) (by decide)
  have hform := etaSkew_eq_skewMat4 h2 η hη (R (gen η 0 1))
  rw [h02, h03, h12, h13, zero_div, zero_div, skewMat4_eq_comb η hη, ← gen_zero_one_eq] at hform
  have key : R (gen η 0 1) =
      ((R (gen η 0 1) : Matrix (Fin 4) (Fin 4) K) 0 1 / η 1) • gen η 0 1 +
        ((R (gen η 0 1) : Matrix (Fin 4) (Fin 4) K) 2 3 / (η 0 * η 1 * η 3)) •
          hodge η (gen η 0 1) :=
    Subtype.ext hform
  have hR' : ∀ X Y : etaSkew η,
      (R - (((R (gen η 0 1) : Matrix (Fin 4) (Fin 4) K) 0 1 / η 1) •
          (LinearMap.id : etaSkew η →ₗ[K] etaSkew η) +
        ((R (gen η 0 1) : Matrix (Fin 4) (Fin 4) K) 2 3 / (η 0 * η 1 * η 3)) • hodge η)) ⁅X, Y⁆ =
      ⁅X, (R - (((R (gen η 0 1) : Matrix (Fin 4) (Fin 4) K) 0 1 / η 1) •
          (LinearMap.id : etaSkew η →ₗ[K] etaSkew η) +
        ((R (gen η 0 1) : Matrix (Fin 4) (Fin 4) K) 2 3 / (η 0 * η 1 * η 3)) • hodge η)) Y⁆ := by
    intro X Y
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      hR, hodge_lie h2 η hη, lie_sub, lie_add, lie_smul]
  have h0 : (R - (((R (gen η 0 1) : Matrix (Fin 4) (Fin 4) K) 0 1 / η 1) •
        (LinearMap.id : etaSkew η →ₗ[K] etaSkew η) +
      ((R (gen η 0 1) : Matrix (Fin 4) (Fin 4) K) 2 3 / (η 0 * η 1 * η 3)) • hodge η))
      (gen η 0 1) = 0 := by
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact key
  exact sub_eq_zero.mp (eq_zero_of_apply_gen_eq_zero h2 η hη _ hR' h01 h0)

end Four

/-- **Control of L5, hypothesis `card ι ≠ 4` deleted.** For a field `K` and `η : Fin 4 → K` with
all entries nonzero, there is no `c` in `K` with `hodge η = c • id`. (With part (i) of L1K,
`hodge η` is a bracket-commuting map that is not a scalar.) -/
theorem centroid_control_card_four {K : Type*} [Field K] (η : Fin 4 → K)
    (hη : ∀ i, η i ≠ 0) : ¬ ∃ c : K, hodge η = c • LinearMap.id := by
  rintro ⟨c, hc⟩
  have hz : (-c) • (LinearMap.id : etaSkew η →ₗ[K] etaSkew η) + (1 : K) • hodge η = 0 := by
    rw [hc]
    module
  exact one_ne_zero (smul_id_add_smul_hodge_eq_zero η hη _ _ hz).2

/-- **L1K.** Let `K` be a field of characteristic zero and `η : Fin 4 → K` with all entries
nonzero. Then, on the Lie algebra `etaSkew η` of `η`-skew `4 × 4` matrices, with
`hodge η X = star0 (diagonal η * X) * diagonal η`:
(i) `hodge η ⁅X, Y⁆ = ⁅X, hodge η Y⁆` for all `X`, `Y`;
(ii) `hodge η (hodge η X) = (∏ i, η i) • X` for all `X`;
(iii) for every `K`-linear endomorphism `R` of `etaSkew η` with `R ⁅X, Y⁆ = ⁅X, R Y⁆` for all `X`,
`Y`, there is exactly one pair `(a, b)` in `K × K` with `R = a • id + b • hodge η`. -/
theorem hodge_centroid_field {K : Type*} [Field K] [CharZero K] (η : Fin 4 → K)
    (hη : ∀ i, η i ≠ 0) :
    (∀ X Y : etaSkew η, hodge η ⁅X, Y⁆ = ⁅X, hodge η Y⁆) ∧
    (∀ X : etaSkew η, hodge η (hodge η X) = (∏ i, η i) • X) ∧
    ∀ R : etaSkew η →ₗ[K] etaSkew η, (∀ X Y : etaSkew η, R ⁅X, Y⁆ = ⁅X, R Y⁆) →
      ∃! ab : K × K, R = ab.1 • LinearMap.id + ab.2 • hodge η := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  refine ⟨hodge_lie h2 η hη, hodge_hodge h2 η hη, ?_⟩
  intro R hR
  have h := eq_smul_id_add_smul_hodge h2 η hη R hR
  refine ⟨(_, _), h, ?_⟩
  rintro ⟨a', b'⟩ h'
  dsimp only at h'
  have hz : (a' - (R (gen η 0 1) : Matrix (Fin 4) (Fin 4) K) 0 1 / η 1) •
        (LinearMap.id : etaSkew η →ₗ[K] etaSkew η) +
      (b' - (R (gen η 0 1) : Matrix (Fin 4) (Fin 4) K) 2 3 / (η 0 * η 1 * η 3)) • hodge η = 0 := by
    have h3 := h'.symm.trans h
    rw [← sub_eq_zero] at h3
    rw [← h3]
    module
  obtain ⟨ha, hb⟩ := smul_id_add_smul_hodge_eq_zero η hη _ _ hz
  exact Prod.ext (sub_eq_zero.mp ha) (sub_eq_zero.mp hb)

/-- **L1.** Let `η : Fin 4 → ℝ` have every entry equal to `1` or `-1`. Then, on the Lie algebra
`etaSkew η` of `η`-skew real `4 × 4` matrices, with
`hodge η X = star0 (diagonal η * X) * diagonal η`:
(i) `hodge η ⁅X, Y⁆ = ⁅X, hodge η Y⁆` for all `X`, `Y`;
(ii) `hodge η (hodge η X) = (∏ i, η i) • X` for all `X`;
(iii) for every real-linear endomorphism `R` of `etaSkew η` with `R ⁅X, Y⁆ = ⁅X, R Y⁆` for all
`X`, `Y`, there is exactly one pair `(a, b)` in `ℝ × ℝ` with `R = a • id + b • hodge η`. -/
theorem hodge_centroid_real (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1) :
    (∀ X Y : etaSkew η, hodge η ⁅X, Y⁆ = ⁅X, hodge η Y⁆) ∧
    (∀ X : etaSkew η, hodge η (hodge η X) = (∏ i, η i) • X) ∧
    ∀ R : etaSkew η →ₗ[ℝ] etaSkew η, (∀ X Y : etaSkew η, R ⁅X, Y⁆ = ⁅X, R Y⁆) →
      ∃! ab : ℝ × ℝ, R = ab.1 • LinearMap.id + ab.2 • hodge η := by
  exact hodge_centroid_field η fun i => by rcases hη i with h | h <;> rw [h] <;> norm_num

/-! ### The dimension of `etaSkew η`, and the determinant at `so' (Fin 4) (Fin 2) ℝ` -/

section Finrank

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The entries of an `η`-skew matrix at the positions `(i, j)` with `rk i < rk j`. -/
def upperEntries (η : ι → K) (rk : ι → ℕ) :
    etaSkew η →ₗ[K] ({p : ι × ι // rk p.1 < rk p.2} → K) where
  toFun X p := (X : Matrix ι ι K) p.1.1 p.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The `η`-skew matrix with prescribed entries at the positions `(i, j)` with `rk i < rk j`. -/
def ofUpperEntries (η : ι → K) (rk : ι → ℕ) (f : {p : ι × ι // rk p.1 < rk p.2} → K) :
    Matrix ι ι K :=
  fun i j => if h : rk i < rk j then f ⟨(i, j), h⟩
    else if h' : rk j < rk i then -(η j * f ⟨(j, i), h'⟩ / η i) else 0

/-- `ofUpperEntries η rk f` is `η`-skew. -/
theorem ofUpperEntries_mem (η : ι → K) (hη : ∀ i, η i ≠ 0) (rk : ι → ℕ)
    (f : {p : ι × ι // rk p.1 < rk p.2} → K) : ofUpperEntries η rk f ∈ etaSkew η := by
  rw [mem_etaSkew_iff]
  intro i j
  have hi := hη i
  have hj := hη j
  rcases lt_trichotomy (rk i) (rk j) with h | h | h
  · simp only [ofUpperEntries, dite_eq_left h, dite_eq_right (not_lt.mpr h.le)]
    field_simp
  · simp only [ofUpperEntries, h, lt_irrefl, dite_false, zero_mul, mul_zero, neg_zero]
  · simp only [ofUpperEntries, dite_eq_left h, dite_eq_right (not_lt.mpr h.le)]
    field_simp

/-- For an injective `rk : ι → ℕ`, the `η`-skew matrices have dimension the number of pairs
`(i, j)` with `rk i < rk j`. -/
theorem finrank_etaSkew (h2 : (2 : K) ≠ 0) (η : ι → K) (hη : ∀ i, η i ≠ 0) (rk : ι → ℕ)
    (hrk : Function.Injective rk) :
    Module.finrank K (etaSkew η) = Fintype.card {p : ι × ι // rk p.1 < rk p.2} := by
  have hinj : Function.Injective (upperEntries η rk) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX0
    have hX := (mem_etaSkew_iff η X.1).mp X.2
    have hup : ∀ i j, rk i < rk j → (X : Matrix ι ι K) i j = 0 := fun i j hij =>
      congrFun hX0 ⟨(i, j), hij⟩
    apply Subtype.ext
    ext i j
    rcases lt_trichotomy (rk i) (rk j) with h | h | h
    · exact hup i j h
    · rw [hrk h]
      exact etaSkew_apply_self h2 η hη X j
    · have h3 := hX j i
      rw [hup j i h, mul_zero, neg_zero] at h3
      exact (mul_eq_zero.mp h3).resolve_right (hη i)
  have hsurj : Function.Surjective (upperEntries η rk) := by
    intro f
    refine ⟨⟨ofUpperEntries η rk f, ofUpperEntries_mem η hη rk f⟩, ?_⟩
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    exact dite_eq_left h
  exact (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).finrank_eq.trans
    (Module.finrank_fintype_fun_eq_card K)

/-- The Lie algebra `so' (Fin 4) (Fin 2) ℝ` has dimension `15`. -/
theorem finrank_so'_four_two :
    Module.finrank ℝ (LieAlgebra.Orthogonal.so' (Fin 4) (Fin 2) ℝ) = 15 := by
  have h := finrank_etaSkew (K := ℝ) two_ne_zero
    (Sum.elim (fun _ : Fin 4 => (1 : ℝ)) fun _ : Fin 2 => (-1 : ℝ))
    (by rintro (i | i) <;> simp)
    (Sum.elim (fun i : Fin 4 => (i : ℕ)) fun j : Fin 2 => 4 + (j : ℕ))
    (by decide)
  rw [show Fintype.card {p : (Fin 4 ⊕ Fin 2) × (Fin 4 ⊕ Fin 2) //
      Sum.elim (fun i : Fin 4 => (i : ℕ)) (fun j : Fin 2 => 4 + (j : ℕ)) p.1 <
        Sum.elim (fun i : Fin 4 => (i : ℕ)) (fun j : Fin 2 => 4 + (j : ℕ)) p.2} = 15 from by
    decide] at h
  exact h

end Finrank

/-- **L5, at `so' (Fin 4) (Fin 2) ℝ`, with the determinant.** Let `R` be a real-linear
endomorphism of `so' (Fin 4) (Fin 2) ℝ` with `R ⁅X, Y⁆ = ⁅X, R Y⁆` for all `X`, `Y`. Then there is
a real `c` with `R = c • id` and `LinearMap.det R = c ^ 15`. -/
theorem centroid_scalar_so'_four_two
    (R : LieAlgebra.Orthogonal.so' (Fin 4) (Fin 2) ℝ →ₗ[ℝ]
         LieAlgebra.Orthogonal.so' (Fin 4) (Fin 2) ℝ)
    (hR : ∀ X Y : LieAlgebra.Orthogonal.so' (Fin 4) (Fin 2) ℝ, R ⁅X, Y⁆ = ⁅X, R Y⁆) :
    ∃ c : ℝ, R = c • LinearMap.id ∧ LinearMap.det R = c ^ 15 := by
  obtain ⟨c, hc⟩ := centroid_scalar_so' (p := Fin 4) (q := Fin 2) (by simp) R hR
  refine ⟨c, hc, ?_⟩
  rw [hc, LinearMap.det_smul, finrank_so'_four_two, LinearMap.det_id, mul_one]

end LorentzLie
