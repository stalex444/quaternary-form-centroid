module
public import Mathlib
public import HermiteCompositum.Defs

@[expose] public section

/-!
# Hermite's signature theorem

For a real polynomial `f` of degree `n`, the Hermite form is the quadratic form on `ℝⁿ`
with Hankel matrix of power sums, `H_f(c) = ∑_{i,j<n} s_{i+j} c_i c_j`, where
`s_k = ∑_α α^k` runs over the complex roots of `f` with multiplicity.

**Theorem (Hermite, 1853/1856; Sylvester 1853).** With `D` the set of distinct complex
roots, `R = {α ∈ D | α real}` and `C⁺ = {α ∈ D | Im α > 0}`,
* `sigPos H_f = #R + #C⁺`,
* `sigNeg H_f = #C⁺`,
* `finrank (radical H_f) = n − #D`.

So the rank of `H_f` is the number of distinct roots, and its signature
(`sigPos − sigNeg`) is the number of distinct real roots. The non-squarefree case is
included: multiplicities only rescale the squares, and the radical has dimension `n − #D`.

**Proof.** `H_f(c) = Re ∑_α m_α ℓ_α(c)²` with `ℓ_α(c) = ∑ c_i α^i` and `m_α` the multiplicity
(H2). Writing `ℓ_α = u_α + i v_α`, a real root contributes `m_α u_α²`, and a conjugate pair
`{β, β̄}` contributes `2 m_β (u_β² − v_β²)` (H3). The `#R + 2 #C⁺` real linear forms
`{u_α (α ∈ R), u_β, v_β (β ∈ C⁺)}` are linearly independent: this is proved by Lagrange
interpolation over `ℂ` followed by conjugation-symmetrisation, which produces a real
coefficient vector with prescribed values (H4). Completing them by a basis of their common
kernel gives an isometry of `H_f` with a weighted sum of squares with weights
`(m_α, 2m_β, −2m_β, 0, …)` (H5), and Sylvester's law of inertia
(`QuadraticForm.sigPos_of_equiv_weightedSumSquares`) counts (H6).

No monic hypothesis is needed: the complex roots with multiplicity and `natDegree` of a
nonzero real polynomial do not depend on its leading coefficient, and the zero polynomial
gives the zero form on `Fin 0 → ℝ`.
-/

namespace HermiteCompositum

open Polynomial Finset
open scoped ComplexConjugate

noncomputable section

/-! ### Definitions -/

-- `croots`, `powerSum`, `hermiteMatrix`, `hermiteForm`, `distinctRoots`, `realRoots` and
-- `upperRoots` are defined in `HermiteCompositum/Defs.lean` (shared verbatim with `Challenge.lean`).

/-- `C⁻`: the distinct roots in the open lower half plane (auxiliary). -/
def lowerRoots (f : ℝ[X]) : Finset ℂ := (distinctRoots f).filter (fun z => z.im < 0)

/-! ### H1: the root multiset is conjugation-invariant -/

theorem card_croots (f : ℝ[X]) : Multiset.card (croots f) = f.natDegree := by
  unfold croots
  rw [IsAlgClosed.card_roots_eq_natDegree,
    natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]

theorem croots_map_conj (f : ℝ[X]) : (croots f).map conj = croots f := by
  unfold croots
  rw [roots_map_of_injective_of_card_eq_natDegree (starRingEnd ℂ).injective
    IsAlgClosed.card_roots_eq_natDegree, Polynomial.map_map]
  have h : (starRingEnd ℂ).comp (algebraMap ℝ ℂ) = algebraMap ℝ ℂ :=
    RingHom.ext fun r => by simp
  rw [h]

theorem count_conj_croots (f : ℝ[X]) (z : ℂ) :
    (croots f).count (conj z) = (croots f).count z := by
  conv_lhs => rw [← croots_map_conj f]
  exact Multiset.count_map_eq_count' _ _ (starRingEnd ℂ).injective z

theorem mem_distinctRoots {f : ℝ[X]} {z : ℂ} : z ∈ distinctRoots f ↔ z ∈ croots f :=
  Multiset.mem_toFinset

/-- `D` is Mathlib's root set of `f` over `ℂ`. -/
theorem coe_distinctRoots (f : ℝ[X]) : (distinctRoots f : Set ℂ) = f.rootSet ℂ := by
  rw [rootSet_def, aroots_def]; rfl

theorem conj_mem_distinctRoots {f : ℝ[X]} {z : ℂ} :
    conj z ∈ distinctRoots f ↔ z ∈ distinctRoots f := by
  simp only [mem_distinctRoots, ← Multiset.count_pos, count_conj_croots]

theorem count_pos_of_mem_distinctRoots {f : ℝ[X]} {z : ℂ} (hz : z ∈ distinctRoots f) :
    0 < (croots f).count z :=
  Multiset.count_pos.mpr (mem_distinctRoots.mp hz)

theorem card_distinctRoots_le (f : ℝ[X]) : (distinctRoots f).card ≤ f.natDegree :=
  (Multiset.toFinset_card_le _).trans (card_croots f).le

theorem realRoots_subset (f : ℝ[X]) : realRoots f ⊆ distinctRoots f := filter_subset _ _
theorem upperRoots_subset (f : ℝ[X]) : upperRoots f ⊆ distinctRoots f := filter_subset _ _

theorem mem_realRoots {f : ℝ[X]} {z : ℂ} :
    z ∈ realRoots f ↔ z ∈ distinctRoots f ∧ z.im = 0 := mem_filter
theorem mem_upperRoots {f : ℝ[X]} {z : ℂ} :
    z ∈ upperRoots f ↔ z ∈ distinctRoots f ∧ 0 < z.im := mem_filter
theorem mem_lowerRoots {f : ℝ[X]} {z : ℂ} :
    z ∈ lowerRoots f ↔ z ∈ distinctRoots f ∧ z.im < 0 := mem_filter

theorem lowerRoots_eq_image_conj (f : ℝ[X]) :
    lowerRoots f = (upperRoots f).image conj := by
  ext z
  simp only [mem_lowerRoots, mem_image, mem_upperRoots]
  constructor
  · rintro ⟨hz, hlt⟩
    exact ⟨conj z, ⟨conj_mem_distinctRoots.mpr hz, by simp [hlt]⟩, Complex.conj_conj z⟩
  · rintro ⟨β, ⟨hβ, hpos⟩, rfl⟩
    exact ⟨conj_mem_distinctRoots.mpr hβ, by simp [hpos]⟩

theorem card_lowerRoots (f : ℝ[X]) : (lowerRoots f).card = (upperRoots f).card := by
  rw [lowerRoots_eq_image_conj, card_image_of_injective _ (starRingEnd ℂ).injective]

theorem filter_filter_upper (f : ℝ[X]) :
    ((distinctRoots f).filter (fun z => ¬ z.im = 0)).filter (fun z => 0 < z.im)
      = upperRoots f := by
  rw [filter_filter]
  exact filter_congr fun z _ => ⟨fun h => h.2, fun h => ⟨h.ne', h⟩⟩

theorem filter_filter_lower (f : ℝ[X]) :
    ((distinctRoots f).filter (fun z => ¬ z.im = 0)).filter (fun z => ¬ 0 < z.im)
      = lowerRoots f := by
  rw [filter_filter]
  exact filter_congr fun z _ => ⟨fun h => lt_of_le_of_ne (not_lt.mp h.2) h.1,
    fun h => ⟨h.ne, not_lt.mpr h.le⟩⟩

/-- `#D = #R + 2 #C⁺`. -/
theorem card_distinctRoots (f : ℝ[X]) :
    (distinctRoots f).card = (realRoots f).card + 2 * (upperRoots f).card := by
  have h1 := card_filter_add_card_filter_not (s := distinctRoots f)
    (fun z : ℂ => z.im = 0)
  have h2 := card_filter_add_card_filter_not
    (s := (distinctRoots f).filter (fun z : ℂ => ¬ z.im = 0)) (fun z : ℂ => 0 < z.im)
  rw [filter_filter_upper, filter_filter_lower, card_lowerRoots] at h2
  unfold realRoots
  omega

/-! ### The linear forms `ℓ_α`, `u_α`, `v_α` -/

/-- The complex-valued real-linear form `c ↦ ∑_{i<n} c_i α^i`. -/
def evalForm (n : ℕ) (α : ℂ) : (Fin n → ℝ) →ₗ[ℝ] ℂ :=
  ∑ i : Fin n, (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ).smulRight (α ^ (i : ℕ))

theorem evalForm_apply {n : ℕ} (α : ℂ) (c : Fin n → ℝ) :
    evalForm n α c = ∑ i : Fin n, (c i : ℂ) * α ^ (i : ℕ) := by
  simp [evalForm, LinearMap.sum_apply, Complex.real_smul]

/-- `u_α = Re ℓ_α`. -/
def reForm (n : ℕ) (α : ℂ) : (Fin n → ℝ) →ₗ[ℝ] ℝ := Complex.reLm ∘ₗ evalForm n α

/-- `v_α = Im ℓ_α`. -/
def imForm (n : ℕ) (α : ℂ) : (Fin n → ℝ) →ₗ[ℝ] ℝ := Complex.imLm ∘ₗ evalForm n α

@[simp] theorem reForm_apply {n : ℕ} (α : ℂ) (c : Fin n → ℝ) :
    reForm n α c = (evalForm n α c).re := rfl

@[simp] theorem imForm_apply {n : ℕ} (α : ℂ) (c : Fin n → ℝ) :
    imForm n α c = (evalForm n α c).im := rfl

theorem evalForm_conj {n : ℕ} (α : ℂ) (c : Fin n → ℝ) :
    evalForm n (conj α) c = conj (evalForm n α c) := by
  simp only [evalForm_apply, map_sum, map_mul, map_pow, Complex.conj_ofReal]

theorem reForm_conj {n : ℕ} (α : ℂ) (c : Fin n → ℝ) :
    reForm n (conj α) c = reForm n α c := by
  simp [evalForm_conj]

theorem imForm_conj {n : ℕ} (α : ℂ) (c : Fin n → ℝ) :
    imForm n (conj α) c = - imForm n α c := by
  simp [evalForm_conj]

theorem imForm_eq_zero_of_im_eq_zero {n : ℕ} {α : ℂ} (h : α.im = 0) (c : Fin n → ℝ) :
    imForm n α c = 0 := by
  have h1 := imForm_conj (n := n) α c
  rw [Complex.conj_eq_iff_im.mpr h] at h1
  linarith

/-! ### H2: `H_f(c) = ∑_{α ∈ D} m_α (u_α(c)² − v_α(c)²)` -/

theorem hermiteForm_apply (f : ℝ[X]) (c : Fin f.natDegree → ℝ) :
    hermiteForm f c = ∑ i : Fin f.natDegree, ∑ j : Fin f.natDegree,
      powerSum f ((i : ℕ) + (j : ℕ)) * c i * c j := by
  simp only [hermiteForm, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply, hermiteMatrix, Matrix.of_apply, smul_eq_mul]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

@[simp] theorem hermiteMatrix_apply (f : ℝ[X]) (i j : Fin f.natDegree) :
    hermiteMatrix f i j = powerSum f ((i : ℕ) + (j : ℕ)) := rfl

theorem hermiteForm_def (f : ℝ[X]) : hermiteForm f = (hermiteMatrix f).toQuadraticForm' := rfl

/-- The power sums of the complex roots are real: `conj ∑ α^k = ∑ α^k`. -/
theorem conj_sum_pow_croots (f : ℝ[X]) (k : ℕ) :
    conj (((croots f).map (· ^ k)).sum) = ((croots f).map (· ^ k)).sum := by
  rw [map_multiset_sum, Multiset.map_map]
  conv_rhs => rw [← croots_map_conj f, Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun α _ => by simp

/-- `powerSum f k`, cast to `ℂ`, is the full complex power sum `∑_α α^k` (with multiplicity). -/
theorem ofReal_powerSum (f : ℝ[X]) (k : ℕ) :
    (powerSum f k : ℂ) = ((croots f).map (· ^ k)).sum :=
  Complex.conj_eq_iff_re.mp (conj_sum_pow_croots f k)

theorem powerSum_eq_re_sum (f : ℝ[X]) (k : ℕ) :
    powerSum f k = (∑ α ∈ distinctRoots f, ((croots f).count α : ℂ) * α ^ k).re := by
  unfold powerSum distinctRoots
  rw [sum_multiset_map_count]
  simp only [nsmul_eq_mul]

/-- The complex identity `∑_{i,j} c_i c_j s_{i+j} = ∑_{α∈D} m_α ℓ_α(c)²`. -/
theorem sum_count_mul_evalForm_sq (f : ℝ[X]) (c : Fin f.natDegree → ℝ) :
    ∑ α ∈ distinctRoots f, ((croots f).count α : ℂ) * (evalForm f.natDegree α c) ^ 2
      = ∑ i : Fin f.natDegree, ∑ j : Fin f.natDegree, (c i : ℂ) * (c j : ℂ) *
          ∑ α ∈ distinctRoots f, ((croots f).count α : ℂ) * α ^ ((i : ℕ) + (j : ℕ)) := by
  simp only [evalForm_apply, sq]
  simp only [sum_mul_sum]
  simp only [mul_sum]
  conv_lhs => rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  conv_lhs => rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun α _ => ?_
  rw [pow_add]; ring

theorem hermiteForm_eq_sum_distinctRoots (f : ℝ[X]) (c : Fin f.natDegree → ℝ) :
    hermiteForm f c = ∑ α ∈ distinctRoots f,
      ((croots f).count α : ℝ) * (reForm f.natDegree α c ^ 2 - imForm f.natDegree α c ^ 2) := by
  have h : hermiteForm f c
      = (∑ α ∈ distinctRoots f, ((croots f).count α : ℂ) * (evalForm f.natDegree α c) ^ 2).re := by
    rw [hermiteForm_apply, sum_count_mul_evalForm_sq, Complex.re_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [powerSum_eq_re_sum, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    ring
  rw [h, Complex.re_sum]
  refine sum_congr rfl fun α _ => ?_
  rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul, reForm_apply, imForm_apply, sq, sq, sq,
    Complex.mul_re]

/-! ### H3: conjugate pairing -/

/-- `m_{β̄} = m_β`, `u_{β̄} = u_β`, `v_{β̄} = −v_β`: the lower half-plane sum equals the upper one. -/
theorem sum_lowerRoots_eq (f : ℝ[X]) (c : Fin f.natDegree → ℝ) :
    ∑ α ∈ lowerRoots f, ((croots f).count α : ℝ) *
        (reForm f.natDegree α c ^ 2 - imForm f.natDegree α c ^ 2)
      = ∑ β ∈ upperRoots f, ((croots f).count β : ℝ) *
        (reForm f.natDegree β c ^ 2 - imForm f.natDegree β c ^ 2) := by
  rw [lowerRoots_eq_image_conj, sum_image (fun _ _ _ _ h => (starRingEnd ℂ).injective h)]
  refine sum_congr rfl fun β _ => ?_
  rw [count_conj_croots, reForm_conj, imForm_conj, neg_sq]

/-- `H_f(c) = ∑_{α∈R} m_α u_α² + ∑_{β∈C⁺} 2m_β u_β² + ∑_{β∈C⁺} (−2m_β) v_β²`. -/
theorem hermiteForm_eq_split (f : ℝ[X]) (c : Fin f.natDegree → ℝ) :
    hermiteForm f c
      = ∑ α ∈ realRoots f, ((croots f).count α : ℝ) * reForm f.natDegree α c ^ 2
        + ∑ β ∈ upperRoots f, (2 * ((croots f).count β : ℝ)) * reForm f.natDegree β c ^ 2
        + ∑ β ∈ upperRoots f, (-(2 * ((croots f).count β : ℝ))) * imForm f.natDegree β c ^ 2 := by
  rw [hermiteForm_eq_sum_distinctRoots,
    ← sum_filter_add_sum_filter_not (distinctRoots f) (fun z => z.im = 0),
    ← sum_filter_add_sum_filter_not ((distinctRoots f).filter (fun z => ¬ z.im = 0))
      (fun z => 0 < z.im),
    filter_filter_upper, filter_filter_lower, sum_lowerRoots_eq]
  have h1 : ∑ α ∈ (distinctRoots f).filter (fun z => z.im = 0), ((croots f).count α : ℝ) *
        (reForm f.natDegree α c ^ 2 - imForm f.natDegree α c ^ 2)
      = ∑ α ∈ realRoots f, ((croots f).count α : ℝ) * reForm f.natDegree α c ^ 2 := by
    refine sum_congr rfl fun α hα => ?_
    rw [imForm_eq_zero_of_im_eq_zero (mem_realRoots.mp hα).2, zero_pow two_ne_zero, sub_zero]
  rw [h1, add_assoc]
  congr 1
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun β _ => ?_
  ring

/-! ### H4: the realified Vandermonde forms are linearly independent -/

/-- The index type of the independent linear forms: `R ⊕ (C⁺ ⊕ C⁺)`. -/
abbrev RootIndex (f : ℝ[X]) : Type := ↥(realRoots f) ⊕ (↥(upperRoots f) ⊕ ↥(upperRoots f))

/-- The linear forms `u_α (α ∈ R)`, `u_β`, `v_β (β ∈ C⁺)`. -/
def rootForm (f : ℝ[X]) : RootIndex f → ((Fin f.natDegree → ℝ) →ₗ[ℝ] ℝ) :=
  Sum.elim (fun α => reForm f.natDegree α)
    (Sum.elim (fun β => reForm f.natDegree β) (fun β => imForm f.natDegree β))

/-- The weights `m_α`, `2 m_β`, `−2 m_β`. -/
def rootWeight (f : ℝ[X]) : RootIndex f → ℝ :=
  Sum.elim (fun α => ((croots f).count (α : ℂ) : ℝ))
    (Sum.elim (fun β => 2 * ((croots f).count (β : ℂ) : ℝ))
      (fun β => -(2 * ((croots f).count (β : ℂ) : ℝ))))

/-- The evaluation map `c ↦ (ℓ_i(c))_i` into `RootIndex f → ℝ`. -/
def rootMap (f : ℝ[X]) : (Fin f.natDegree → ℝ) →ₗ[ℝ] (RootIndex f → ℝ) :=
  LinearMap.pi (rootForm f)

@[simp] theorem rootMap_apply_inl (f : ℝ[X]) (c : Fin f.natDegree → ℝ) (α : ↥(realRoots f)) :
    rootMap f c (Sum.inl α) = reForm f.natDegree α c := rfl
@[simp] theorem rootMap_apply_inr_inl (f : ℝ[X]) (c : Fin f.natDegree → ℝ)
    (β : ↥(upperRoots f)) : rootMap f c (Sum.inr (Sum.inl β)) = reForm f.natDegree β c := rfl
@[simp] theorem rootMap_apply_inr_inr (f : ℝ[X]) (c : Fin f.natDegree → ℝ)
    (β : ↥(upperRoots f)) : rootMap f c (Sum.inr (Sum.inr β)) = imForm f.natDegree β c := rfl

theorem hermiteForm_eq_sum_rootWeight (f : ℝ[X]) (c : Fin f.natDegree → ℝ) :
    hermiteForm f c = ∑ i, rootWeight f i * (rootMap f c i * rootMap f c i) := by
  rw [hermiteForm_eq_split, Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc,
    ← sum_coe_sort (realRoots f), ← sum_coe_sort (upperRoots f), ← sum_coe_sort (upperRoots f)]
  simp only [rootWeight, Sum.elim_inl, Sum.elim_inr, rootMap_apply_inl, rootMap_apply_inr_inl,
    rootMap_apply_inr_inr, sq]

/-- **H4.** The evaluation map is surjective, i.e. the forms `u_α (α ∈ R)`, `u_β`, `v_β (β ∈ C⁺)`
are linearly independent. Proof: Lagrange-interpolate the prescribed values (extended to
`D` by conjugate symmetry) over `ℂ`, then take real parts of the coefficients. -/
theorem rootMap_surjective (f : ℝ[X]) : Function.Surjective (rootMap f) := by
  classical
  intro y
  let y₁ : ℂ → ℝ := fun z => if h : z ∈ realRoots f then y (Sum.inl ⟨z, h⟩) else 0
  let y₂ : ℂ → ℝ := fun z => if h : z ∈ upperRoots f then y (Sum.inr (Sum.inl ⟨z, h⟩)) else 0
  let y₃ : ℂ → ℝ := fun z => if h : z ∈ upperRoots f then y (Sum.inr (Sum.inr ⟨z, h⟩)) else 0
  let r : ℂ → ℂ := fun z =>
    if z.im = 0 then (y₁ z : ℂ)
    else if 0 < z.im then (y₂ z : ℂ) + Complex.I * (y₃ z : ℂ)
    else (y₂ (conj z) : ℂ) - Complex.I * (y₃ (conj z) : ℂ)
  let P : ℂ[X] := Lagrange.interpolate (distinctRoots f) id r
  have hP : ∀ α ∈ distinctRoots f, P.eval α = r α := fun α hα =>
    Lagrange.eval_interpolate_at_node r (Set.injOn_id _) hα
  have hdeg : P.degree < (distinctRoots f).card :=
    Lagrange.degree_interpolate_lt r (Set.injOn_id _)
  let c : Fin f.natDegree → ℝ := fun i => (P.coeff i).re
  have hev : ∀ α ∈ distinctRoots f,
      evalForm f.natDegree α c = (r α + conj (r (conj α))) / 2 := by
    intro α hα
    have hnat : P.natDegree < f.natDegree := by
      rcases eq_or_ne P 0 with h0 | h0
      · rw [h0, natDegree_zero]
        exact lt_of_lt_of_le (card_pos.mpr ⟨α, hα⟩) (card_distinctRoots_le f)
      · exact lt_of_lt_of_le ((natDegree_lt_iff_degree_lt h0).mpr hdeg)
          (card_distinctRoots_le f)
    have h1 : ∑ i : Fin f.natDegree, P.coeff i * α ^ (i : ℕ) = P.eval α := by
      rw [eval_eq_sum_range' hnat, ← Fin.sum_univ_eq_sum_range (fun i => P.coeff i * α ^ i)]
    have h2 : ∑ i : Fin f.natDegree, conj (P.coeff i) * α ^ (i : ℕ)
        = conj (P.eval (conj α)) := by
      have hnat' : (P.map (starRingEnd ℂ)).natDegree < f.natDegree :=
        lt_of_le_of_lt natDegree_map_le hnat
      rw [← eval₂_at_apply, Complex.conj_conj, ← eval_map, eval_eq_sum_range' hnat',
        ← Fin.sum_univ_eq_sum_range (fun i => (P.map (starRingEnd ℂ)).coeff i * α ^ i)]
      simp only [coeff_map]
    rw [evalForm_apply]
    calc ∑ i : Fin f.natDegree, ((P.coeff i).re : ℂ) * α ^ (i : ℕ)
        = ∑ i : Fin f.natDegree, ((P.coeff i + conj (P.coeff i)) / 2) * α ^ (i : ℕ) := by
          simp_rw [Complex.re_eq_add_conj]
      _ = (∑ i : Fin f.natDegree, P.coeff i * α ^ (i : ℕ)
            + ∑ i : Fin f.natDegree, conj (P.coeff i) * α ^ (i : ℕ)) / 2 := by
          rw [← sum_add_distrib, sum_div]
          refine sum_congr rfl fun i _ => ?_
          ring
      _ = (r α + conj (r (conj α))) / 2 := by
          rw [h1, h2, hP α hα, hP _ (conj_mem_distinctRoots.mpr hα)]
  refine ⟨c, ?_⟩
  funext i
  rcases i with ⟨α, hα⟩ | ⟨β, hβ⟩ | ⟨β, hβ⟩
  · -- a real root: `u_α(c) = y₁ α`
    have hα' := mem_realRoots.mp hα
    have hconj : conj α = α := Complex.conj_eq_iff_im.mpr hα'.2
    have hr : r α = (y₁ α : ℂ) := ite_eq_left hα'.2
    rw [rootMap_apply_inl, reForm_apply, hev α hα'.1, hconj, hr, Complex.conj_ofReal,
      show ((y₁ α : ℂ) + (y₁ α : ℂ)) / 2 = (y₁ α : ℂ) by ring, Complex.ofReal_re]
    exact dite_eq_left hα
  · -- an upper root, real part: `u_β(c) = y₂ β`
    have hβ' := mem_upperRoots.mp hβ
    have hr : r β = (y₂ β : ℂ) + Complex.I * (y₃ β : ℂ) := by
      simp only [r, ite_eq_right hβ'.2.ne', ite_eq_left hβ'.2]
    have hr' : r (conj β) = (y₂ β : ℂ) - Complex.I * (y₃ β : ℂ) := by
      have h1 : ¬ (conj β).im = 0 := by
        rw [Complex.conj_im]; exact neg_ne_zero.mpr hβ'.2.ne'
      have h2 : ¬ 0 < (conj β).im := by
        rw [Complex.conj_im]; exact not_lt.mpr (neg_nonpos.mpr hβ'.2.le)
      simp only [r, ite_eq_right h1, ite_eq_right h2, Complex.conj_conj]
    have hval : ((y₂ β : ℂ) + Complex.I * (y₃ β : ℂ)
        + conj ((y₂ β : ℂ) - Complex.I * (y₃ β : ℂ))) / 2
        = (y₂ β : ℂ) + Complex.I * (y₃ β : ℂ) := by
      simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
    rw [rootMap_apply_inr_inl, reForm_apply, hev β hβ'.1, hr, hr', hval]
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero]
    exact dite_eq_left hβ
  · -- an upper root, imaginary part: `v_β(c) = y₃ β`
    have hβ' := mem_upperRoots.mp hβ
    have hr : r β = (y₂ β : ℂ) + Complex.I * (y₃ β : ℂ) := by
      simp only [r, ite_eq_right hβ'.2.ne', ite_eq_left hβ'.2]
    have hr' : r (conj β) = (y₂ β : ℂ) - Complex.I * (y₃ β : ℂ) := by
      have h1 : ¬ (conj β).im = 0 := by
        rw [Complex.conj_im]; exact neg_ne_zero.mpr hβ'.2.ne'
      have h2 : ¬ 0 < (conj β).im := by
        rw [Complex.conj_im]; exact not_lt.mpr (neg_nonpos.mpr hβ'.2.le)
      simp only [r, ite_eq_right h1, ite_eq_right h2, Complex.conj_conj]
    have hval : ((y₂ β : ℂ) + Complex.I * (y₃ β : ℂ)
        + conj ((y₂ β : ℂ) - Complex.I * (y₃ β : ℂ))) / 2
        = (y₂ β : ℂ) + Complex.I * (y₃ β : ℂ) := by
      simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
    rw [rootMap_apply_inr_inr, imForm_apply, hev β hβ'.1, hr, hr', hval]
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, zero_add]
    exact dite_eq_left hβ

/-! ### H5: completing to an isometry with a weighted sum of squares -/

/-- A linear right inverse of the surjective evaluation map. -/
def rootSection (f : ℝ[X]) : (RootIndex f → ℝ) →ₗ[ℝ] (Fin f.natDegree → ℝ) :=
  LinearMap.splittingOfFunOnFintypeSurjective (rootMap f) (rootMap_surjective f)

theorem rootMap_rootSection (f : ℝ[X]) (y : RootIndex f → ℝ) :
    rootMap f (rootSection f y) = y := by
  have h := LinearMap.congr_fun
    (LinearMap.splittingOfFunOnFintypeSurjective_splits (rootMap f) (rootMap_surjective f)) y
  simpa [rootSection] using h

/-- `ℝⁿ ≃ (RootIndex f → ℝ) × ker (rootMap f)`, via `c ↦ (T c, c − g (T c))`. -/
def prodKerEquiv (f : ℝ[X]) :
    (Fin f.natDegree → ℝ) ≃ₗ[ℝ] (RootIndex f → ℝ) × LinearMap.ker (rootMap f) where
  toFun c := (rootMap f c, ⟨c - rootSection f (rootMap f c), by
    rw [LinearMap.mem_ker, map_sub, rootMap_rootSection, sub_self]⟩)
  invFun p := rootSection f p.1 + p.2
  map_add' a b := by
    refine Prod.ext (by simp) (Subtype.ext ?_)
    simp only [Prod.snd_add, Submodule.coe_add, map_add]
    abel
  map_smul' t a := by
    refine Prod.ext (by simp) (Subtype.ext ?_)
    simp only [RingHom.id_apply, Prod.smul_snd, Submodule.coe_smul, map_smul, smul_sub]
  left_inv c := by simp
  right_inv p := by
    refine Prod.ext ?_ (Subtype.ext ?_)
    · simp [rootMap_rootSection]
    · simp [rootMap_rootSection]

@[simp] theorem prodKerEquiv_apply_fst (f : ℝ[X]) (c : Fin f.natDegree → ℝ) :
    (prodKerEquiv f c).1 = rootMap f c := rfl

/-- The dimension of the common kernel of the forms (it equals `n − #D`, but that is not
needed: the padding weights are zero). -/
abbrev kerDim (f : ℝ[X]) : ℕ := Module.finrank ℝ (LinearMap.ker (rootMap f))

/-- The padded index type `R ⊕ (C⁺ ⊕ C⁺) ⊕ Fin k`. -/
abbrev PaddedIndex (f : ℝ[X]) : Type := RootIndex f ⊕ Fin (kerDim f)

/-- The weights `(m_α, 2m_β, −2m_β, 0, …)`. -/
def paddedWeight (f : ℝ[X]) : PaddedIndex f → ℝ := Sum.elim (rootWeight f) (fun _ => 0)

/-- The linear isomorphism `ℝⁿ ≃ (PaddedIndex f → ℝ)` carrying `H_f` to the weighted sum of
squares. -/
def hermiteEquiv (f : ℝ[X]) : (Fin f.natDegree → ℝ) ≃ₗ[ℝ] (PaddedIndex f → ℝ) :=
  ((prodKerEquiv f).trans
    ((LinearEquiv.refl ℝ _).prodCongr
      (Module.finBasis ℝ (LinearMap.ker (rootMap f))).equivFun)).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).symm

@[simp] theorem hermiteEquiv_apply_inl (f : ℝ[X]) (c : Fin f.natDegree → ℝ) (i : RootIndex f) :
    hermiteEquiv f c (Sum.inl i) = rootMap f c i := rfl

/-- **H5.** `H_f` is isometric to the weighted sum of squares with weights
`(m_α, 2m_β, −2m_β, 0, …)`. -/
theorem hermiteForm_equivalent (f : ℝ[X]) :
    QuadraticMap.Equivalent (hermiteForm f)
      (QuadraticMap.weightedSumSquares ℝ (paddedWeight f)) :=
  ⟨{ hermiteEquiv f with
      map_app' := fun c => by
        rw [QuadraticMap.weightedSumSquares_apply, Fintype.sum_sum_type,
          hermiteForm_eq_sum_rootWeight]
        simp [paddedWeight] }⟩

/-! ### H6: counting -/

/-- **Hermite's signature theorem, positive index**: `sigPos H_f = #R + #C⁺`. -/
theorem sigPos_hermiteForm (f : ℝ[X]) :
    sigPos (hermiteForm f) = (realRoots f).card + (upperRoots f).card := by
  rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares (hermiteForm_equivalent f)]
  have hset : {i | 0 < paddedWeight f i} = ↑(univ.filter fun i => 0 < paddedWeight f i) := by
    ext; simp
  rw [hset, Set.ncard_coe_finset, card_filter, Fintype.sum_sum_type, Fintype.sum_sum_type,
    Fintype.sum_sum_type]
  have h1 : ∀ α : ↥(realRoots f),
      (if 0 < paddedWeight f (Sum.inl (Sum.inl α)) then 1 else 0) = 1 := fun α => ite_eq_left (by
    simp only [paddedWeight, rootWeight, Sum.elim_inl]
    exact_mod_cast count_pos_of_mem_distinctRoots (realRoots_subset f α.2))
  have h2 : ∀ β : ↥(upperRoots f),
      (if 0 < paddedWeight f (Sum.inl (Sum.inr (Sum.inl β))) then 1 else 0) = 1 := fun β =>
    ite_eq_left (by
      simp only [paddedWeight, rootWeight, Sum.elim_inl, Sum.elim_inr]
      have := count_pos_of_mem_distinctRoots (upperRoots_subset f β.2)
      have : (0 : ℝ) < ((croots f).count (β : ℂ) : ℝ) := by exact_mod_cast this
      linarith)
  have h3 : ∀ β : ↥(upperRoots f),
      (if 0 < paddedWeight f (Sum.inl (Sum.inr (Sum.inr β))) then 1 else 0) = 0 := fun β =>
    ite_eq_right (by
      simp only [paddedWeight, rootWeight, Sum.elim_inl, Sum.elim_inr]
      have := count_pos_of_mem_distinctRoots (upperRoots_subset f β.2)
      have : (0 : ℝ) < ((croots f).count (β : ℂ) : ℝ) := by exact_mod_cast this
      linarith)
  have h4 : ∀ j : Fin (kerDim f), (if 0 < paddedWeight f (Sum.inr j) then 1 else 0) = 0 :=
    fun j => ite_eq_right (lt_irrefl 0)
  simp only [h1, h2, h3, h4, sum_const, card_univ, Fintype.card_coe, smul_eq_mul, mul_one,
    mul_zero, add_zero]

/-- **Hermite's signature theorem, negative index**: `sigNeg H_f = #C⁺`. -/
theorem sigNeg_hermiteForm (f : ℝ[X]) :
    sigNeg (hermiteForm f) = (upperRoots f).card := by
  rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares (hermiteForm_equivalent f)]
  have hset : {i | paddedWeight f i < 0} = ↑(univ.filter fun i => paddedWeight f i < 0) := by
    ext; simp
  rw [hset, Set.ncard_coe_finset, card_filter, Fintype.sum_sum_type, Fintype.sum_sum_type,
    Fintype.sum_sum_type]
  have h1 : ∀ α : ↥(realRoots f),
      (if paddedWeight f (Sum.inl (Sum.inl α)) < 0 then 1 else 0) = 0 := fun α => ite_eq_right (by
    simp only [paddedWeight, rootWeight, Sum.elim_inl]
    exact not_lt.mpr (Nat.cast_nonneg _))
  have h2 : ∀ β : ↥(upperRoots f),
      (if paddedWeight f (Sum.inl (Sum.inr (Sum.inl β))) < 0 then 1 else 0) = 0 := fun β =>
    ite_eq_right (by
      simp only [paddedWeight, rootWeight, Sum.elim_inl, Sum.elim_inr]
      exact not_lt.mpr (by positivity))
  have h3 : ∀ β : ↥(upperRoots f),
      (if paddedWeight f (Sum.inl (Sum.inr (Sum.inr β))) < 0 then 1 else 0) = 1 := fun β =>
    ite_eq_left (by
      simp only [paddedWeight, rootWeight, Sum.elim_inl, Sum.elim_inr]
      have := count_pos_of_mem_distinctRoots (upperRoots_subset f β.2)
      have : (0 : ℝ) < ((croots f).count (β : ℂ) : ℝ) := by exact_mod_cast this
      linarith)
  have h4 : ∀ j : Fin (kerDim f), (if paddedWeight f (Sum.inr j) < 0 then 1 else 0) = 0 :=
    fun j => ite_eq_right (lt_irrefl 0)
  simp only [h1, h2, h3, h4, sum_const, card_univ, Fintype.card_coe, smul_eq_mul, mul_one,
    mul_zero, zero_add, add_zero]

/-- **Rank**: `sigPos H_f + sigNeg H_f = #D`, the number of distinct roots. -/
theorem sigPos_add_sigNeg_hermiteForm (f : ℝ[X]) :
    sigPos (hermiteForm f) + sigNeg (hermiteForm f) = (distinctRoots f).card := by
  rw [sigPos_hermiteForm, sigNeg_hermiteForm, card_distinctRoots]; ring

/-- **Hermite's signature theorem, radical**: `finrank (radical H_f) = n − #D`. -/
theorem finrank_radical_hermiteForm (f : ℝ[X]) :
    Module.finrank ℝ (hermiteForm f).radical = f.natDegree - (distinctRoots f).card := by
  have h := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := hermiteForm f)
  rw [sigPos_add_sigNeg_hermiteForm, Module.finrank_fin_fun] at h
  omega

set_option linter.unusedVariables false in
/-- **Hermite's signature theorem** for monic `f` (the shape of the classical statement). The monic
hypothesis is not used: see `sigPos_hermiteForm`, `sigNeg_hermiteForm`,
`finrank_radical_hermiteForm`, which hold for every `f : ℝ[X]`; compared statement 1 of
`Challenge.lean` is their hypothesis-free conjunction. -/
theorem hermite_signature (f : ℝ[X]) (hf : f.Monic) :
    sigPos (hermiteForm f) = (realRoots f).card + (upperRoots f).card ∧
    sigNeg (hermiteForm f) = (upperRoots f).card ∧
    Module.finrank ℝ (hermiteForm f).radical = f.natDegree - (distinctRoots f).card :=
  ⟨sigPos_hermiteForm f, sigNeg_hermiteForm f, finrank_radical_hermiteForm f⟩

end

end HermiteCompositum
