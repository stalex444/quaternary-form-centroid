module
public import Mathlib

@[expose] public section

/-!
# Places of a linearly disjoint compositum; signed discriminant of a coprime compositum

Let `L` be a number field and `K₁ K₂ : IntermediateField ℚ L` with `K₁.LinearDisjoint K₂` and
`K₁ ⊔ K₂ = ⊤`.

* **Statement 3 (places of a linearly disjoint compositum).**
  `nrRealPlaces L = nrRealPlaces K₁ * nrRealPlaces K₂` and
  `2 * nrComplexPlaces L = finrank ℚ K₁ * finrank ℚ K₂ - nrRealPlaces K₁ * nrRealPlaces K₂`.

  Route: linear disjointness and `K₁ ⊔ K₂ = ⊤` give `K₁ ⊗[ℚ] K₂ ≃ₐ[ℚ] L`
  (`Subalgebra.LinearDisjoint.mulMap`); hence restricting an embedding `L →+* ℂ` to the pair of
  embeddings of `K₁` and `K₂` is a bijection (injective because the equalizer of two embeddings
  is a subalgebra containing `K₁ ⊔ K₂ = ⊤`; surjective by the tensor-product universal property
  `Algebra.TensorProduct.productMap`). An embedding is real iff both restrictions are real.
  Then count with `card_real_embeddings` and `card_add_two_mul_card_eq_rank`.

* **Statement 4 (signed discriminant of a coprime compositum).**
  Adding `IsCoprime (discr K₁) (discr K₂)`:
  `discr L = discr K₁ ^ finrank ℚ K₂ * discr K₂ ^ finrank ℚ K₁`.

  Mathlib (X. Roblot 2025, in `Discriminant/Different.lean`, a file of A. Yang's) proves the
  absolute-value form
  `natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow`; that theorem is USED, not re-proved.
  The sign is added here: `sign_discr` gives `sign (discr K) = (-1) ^ nrComplexPlaces K`, and
  statement 3 gives the parity identity
  `nrComplexPlaces L ≡ nrComplexPlaces K₁ * [K₂:ℚ] + nrComplexPlaces K₂ * [K₁:ℚ] (mod 2)`.

* **Instance-ready corollaries.** With `(r₁, r₂) = (1, 1)` and `(2, 1)` the compositum has
  `(r₁, r₂) = (2, 5)`; and `discr L = d₁ ^ n₂ * d₂ ^ n₁` from the values of the sector
  discriminants and degrees.
-/

open Module NumberField NumberField.ComplexEmbedding NumberField.InfinitePlace

open scoped TensorProduct

namespace HermiteCompositum

variable {L : Type*} [Field L] [NumberField L] {K₁ K₂ : IntermediateField ℚ L}

/-! ### The compositum as a tensor product -/

/-- If `K₁ ⊔ K₂ = ⊤` as intermediate fields of a number field, the same holds for the underlying
subalgebras (every element is algebraic over `ℚ`). -/
theorem toSubalgebra_sup_eq_top (h₂ : K₁ ⊔ K₂ = ⊤) :
    K₁.toSubalgebra ⊔ K₂.toSubalgebra = ⊤ := by
  rw [← IntermediateField.sup_toSubalgebra_of_isAlgebraic_right, h₂,
    IntermediateField.top_toSubalgebra]

/-- The field-level isomorphism `K₁ ⊗[ℚ] K₂ ≃ₐ[ℚ] L` of a linearly disjoint compositum,
induced by multiplication in `L`. -/
noncomputable def compositumAlgEquiv (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) :
    K₁ ⊗[ℚ] K₂ ≃ₐ[ℚ] L :=
  ((IntermediateField.linearDisjoint_iff'.1 h₁).mulMap.trans
    (Subalgebra.equivOfEq _ _ (toSubalgebra_sup_eq_top h₂))).trans Subalgebra.topEquiv

@[simp]
theorem compositumAlgEquiv_tmul (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (a : K₁) (b : K₂) :
    compositumAlgEquiv h₁ h₂ (a ⊗ₜ[ℚ] b) = (a : L) * (b : L) := by
  simp only [compositumAlgEquiv, AlgEquiv.trans_apply, Subalgebra.equivOfEq_apply,
    Subalgebra.topEquiv_apply]
  exact Subalgebra.LinearDisjoint.val_mulMap_tmul _ _ _

/-! ### Embeddings of the compositum are pairs of embeddings -/

/-- Restriction of an embedding `L →+* ℂ` to the pair of embeddings of `K₁` and `K₂`. -/
def restrictPair (K₁ K₂ : IntermediateField ℚ L) (φ : L →+* ℂ) :
    (K₁ →+* ℂ) × (K₂ →+* ℂ) :=
  (φ.comp (algebraMap K₁ L), φ.comp (algebraMap K₂ L))

@[simp] theorem restrictPair_fst (φ : L →+* ℂ) :
    (restrictPair K₁ K₂ φ).1 = φ.comp (algebraMap K₁ L) := rfl

@[simp] theorem restrictPair_snd (φ : L →+* ℂ) :
    (restrictPair K₁ K₂ φ).2 = φ.comp (algebraMap K₂ L) := rfl

/-- Two embeddings of `L` that agree on `K₁` and on `K₂` agree on `K₁ ⊔ K₂ = ⊤`.
Only `K₁ ⊔ K₂ = ⊤` is used here, not linear disjointness. -/
theorem restrictPair_injective (h₂ : K₁ ⊔ K₂ = ⊤) :
    Function.Injective (restrictPair K₁ K₂) := by
  intro φ ψ h
  simp only [restrictPair, Prod.mk.injEq] at h
  have hle : K₁.toSubalgebra ⊔ K₂.toSubalgebra ≤
      AlgHom.equalizer φ.toRatAlgHom ψ.toRatAlgHom := by
    refine sup_le ?_ ?_
    · intro x hx
      exact RingHom.congr_fun h.1 ⟨x, hx⟩
    · intro x hx
      exact RingHom.congr_fun h.2 ⟨x, hx⟩
  rw [toSubalgebra_sup_eq_top h₂] at hle
  ext x
  exact hle (Algebra.mem_top (x := x))

/-- Every pair of embeddings of `K₁` and `K₂` extends to an embedding of `L`: this is the
tensor-product universal property through `compositumAlgEquiv`. -/
theorem restrictPair_surjective (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) :
    Function.Surjective (restrictPair K₁ K₂) := by
  rintro ⟨φ₁, φ₂⟩
  let e := compositumAlgEquiv h₁ h₂
  let Φ : L →ₐ[ℚ] ℂ :=
    (Algebra.TensorProduct.productMap φ₁.toRatAlgHom φ₂.toRatAlgHom).comp e.symm.toAlgHom
  refine ⟨Φ.toRingHom, ?_⟩
  simp only [restrictPair, Prod.mk.injEq]
  constructor
  · ext a
    have ha : e.symm (a : L) = a ⊗ₜ[ℚ] (1 : K₂) := by
      rw [AlgEquiv.symm_apply_eq]
      simp [e]
    simp [Φ, ha]
  · ext b
    have hb : e.symm (b : L) = (1 : K₁) ⊗ₜ[ℚ] b := by
      rw [AlgEquiv.symm_apply_eq]
      simp [e]
    simp [Φ, hb]

/-- Embeddings of a linearly disjoint compositum are pairs of embeddings of the factors. -/
noncomputable def embeddingsEquiv (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) :
    (L →+* ℂ) ≃ (K₁ →+* ℂ) × (K₂ →+* ℂ) :=
  Equiv.ofBijective _ ⟨restrictPair_injective h₂, restrictPair_surjective h₁ h₂⟩

@[simp] theorem embeddingsEquiv_apply (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (φ : L →+* ℂ) : embeddingsEquiv h₁ h₂ φ = restrictPair K₁ K₂ φ := rfl

/-- An embedding of the compositum is real iff both of its restrictions are real.
Only `K₁ ⊔ K₂ = ⊤` is used. -/
theorem isReal_iff_restrictPair (h₂ : K₁ ⊔ K₂ = ⊤) (φ : L →+* ℂ) :
    IsReal φ ↔ IsReal (restrictPair K₁ K₂ φ).1 ∧ IsReal (restrictPair K₁ K₂ φ).2 := by
  constructor
  · intro h
    exact ⟨h.comp _, h.comp _⟩
  · rintro ⟨h1, h2⟩
    rw [ComplexEmbedding.isReal_iff] at h1 h2 ⊢
    apply restrictPair_injective h₂
    simp only [restrictPair, Prod.mk.injEq] at h1 h2 ⊢
    exact ⟨by rw [conjugate_comp]; exact h1, by rw [conjugate_comp]; exact h2⟩

/-! ### Counting places (statement 3) -/

open scoped Classical in
/-- Real embeddings of the compositum are pairs of real embeddings. -/
theorem card_real_embeddings_compositum (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) :
    Fintype.card {φ : L →+* ℂ // IsReal φ} =
      Fintype.card {φ : K₁ →+* ℂ // IsReal φ} * Fintype.card {φ : K₂ →+* ℂ // IsReal φ} := by
  rw [← Fintype.card_prod]
  exact Fintype.card_congr
    (((embeddingsEquiv h₁ h₂).subtypeEquiv fun φ => isReal_iff_restrictPair h₂ φ).trans
      Equiv.subtypeProdEquivProd)

/-- The degree of a linearly disjoint compositum is the product of the degrees. -/
theorem finrank_compositum (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) :
    finrank ℚ L = finrank ℚ K₁ * finrank ℚ K₂ := by
  have := h₁.finrank_sup
  rwa [h₂, IntermediateField.finrank_top'] at this

/-- **Statement 3, real places.** The real places of a linearly disjoint compositum are the
pairs of real places of the factors. -/
theorem nrRealPlaces_compositum (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) :
    nrRealPlaces L = nrRealPlaces K₁ * nrRealPlaces K₂ := by
  classical
  rw [← card_real_embeddings, ← card_real_embeddings, ← card_real_embeddings]
  exact card_real_embeddings_compositum h₁ h₂

/-- **Statement 3, complex places (additive form).**
`r₁(K₁) r₁(K₂) + 2 r₂(L) = [K₁:ℚ] [K₂:ℚ]`. -/
theorem nrRealPlaces_mul_add_two_mul_nrComplexPlaces_compositum
    (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) :
    nrRealPlaces K₁ * nrRealPlaces K₂ + 2 * nrComplexPlaces L =
      finrank ℚ K₁ * finrank ℚ K₂ := by
  rw [← nrRealPlaces_compositum h₁ h₂, card_add_two_mul_card_eq_rank, finrank_compositum h₁ h₂]

/-- **Statement 3, complex places (subtractive form).**
`2 r₂(L) = [K₁:ℚ] [K₂:ℚ] - r₁(K₁) r₁(K₂)` (natural-number subtraction; the additive form above
shows it is exact). -/
theorem two_mul_nrComplexPlaces_compositum (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) :
    2 * nrComplexPlaces L = finrank ℚ K₁ * finrank ℚ K₂ - nrRealPlaces K₁ * nrRealPlaces K₂ := by
  have := nrRealPlaces_mul_add_two_mul_nrComplexPlaces_compositum h₁ h₂
  omega

/-- **Statement 3 (places of a linearly disjoint compositum)**, both parts. -/
theorem places_compositum (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) :
    nrRealPlaces L = nrRealPlaces K₁ * nrRealPlaces K₂ ∧
      2 * nrComplexPlaces L =
        finrank ℚ K₁ * finrank ℚ K₂ - nrRealPlaces K₁ * nrRealPlaces K₂ :=
  ⟨nrRealPlaces_compositum h₁ h₂, two_mul_nrComplexPlaces_compositum h₁ h₂⟩

/-- **Instance-ready corollary of statement 3.** Sectors with `(r₁, r₂) = (1, 1)` and `(2, 1)`
(degrees `3` and `4`) have a linearly disjoint compositum with `(r₁, r₂) = (2, 5)`. -/
theorem places_compositum_of_one_one_two_one (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (hr₁ : nrRealPlaces K₁ = 1) (hc₁ : nrComplexPlaces K₁ = 1)
    (hr₂ : nrRealPlaces K₂ = 2) (hc₂ : nrComplexPlaces K₂ = 1) :
    nrRealPlaces L = 2 ∧ nrComplexPlaces L = 5 := by
  have e1 := card_add_two_mul_card_eq_rank K₁
  have e2 := card_add_two_mul_card_eq_rank K₂
  have e3 := nrRealPlaces_mul_add_two_mul_nrComplexPlaces_compositum h₁ h₂
  have e4 := nrRealPlaces_compositum h₁ h₂
  rw [← e1, ← e2] at e3
  rw [hr₁, hc₁, hr₂, hc₂] at e3
  rw [hr₁, hr₂] at e4
  omega

/-! ### The signed discriminant (statement 4) -/

/-- The parity identity behind the sign: if `a₁ a₂ + 2 c = (a₁ + 2 b₁)(a₂ + 2 b₂)`, then
`c ≡ b₁ (a₂ + 2 b₂) + b₂ (a₁ + 2 b₁) (mod 2)`, as an identity of signs. -/
theorem neg_one_pow_parity_aux (a₁ b₁ a₂ b₂ c : ℕ)
    (h : a₁ * a₂ + 2 * c = (a₁ + 2 * b₁) * (a₂ + 2 * b₂)) :
    (-1 : ℤ) ^ c = (-1) ^ (b₁ * (a₂ + 2 * b₂) + b₂ * (a₁ + 2 * b₁)) := by
  have hc : c = (a₁ * b₂ + b₁ * a₂) + 2 * (b₁ * b₂) := by
    have h' : ((a₁ * a₂ + 2 * c : ℕ) : ℤ) = ((a₁ + 2 * b₁) * (a₂ + 2 * b₂) : ℕ) := by
      exact_mod_cast h
    push_cast at h'
    have h2 : (2 * c : ℤ) = 2 * ((a₁ * b₂ + b₁ * a₂) + 2 * (b₁ * b₂)) := by
      linear_combination h'
    have h3 : 2 * c = 2 * ((a₁ * b₂ + b₁ * a₂) + 2 * (b₁ * b₂)) := by exact_mod_cast h2
    omega
  have he : b₁ * (a₂ + 2 * b₂) + b₂ * (a₁ + 2 * b₁) =
      (a₁ * b₂ + b₁ * a₂) + 2 * (2 * (b₁ * b₂)) := by ring
  rw [hc, he]
  simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

/-- The parity identity for places: `(-1) ^ r₂(L) = (-1) ^ (r₂(K₁) [K₂:ℚ] + r₂(K₂) [K₁:ℚ])`. -/
theorem neg_one_pow_nrComplexPlaces_compositum (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) :
    (-1 : ℤ) ^ nrComplexPlaces L =
      (-1) ^ (nrComplexPlaces K₁ * finrank ℚ K₂ + nrComplexPlaces K₂ * finrank ℚ K₁) := by
  have e1 := card_add_two_mul_card_eq_rank K₁
  have e2 := card_add_two_mul_card_eq_rank K₂
  have e3 := nrRealPlaces_mul_add_two_mul_nrComplexPlaces_compositum h₁ h₂
  rw [← e1, ← e2] at e3
  rw [← e1, ← e2]
  exact neg_one_pow_parity_aux _ _ _ _ _ e3

/-- **Statement 4 (signed discriminant of a coprime compositum).**
`discr L = discr K₁ ^ [K₂:ℚ] * discr K₂ ^ [K₁:ℚ]`, with the sign.

The absolute value is Mathlib's `NumberField.natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow`
(used, not re-proved); the sign is `NumberField.sign_discr` on each side together with the parity
identity `neg_one_pow_nrComplexPlaces_compositum`, which comes from statement 3. -/
theorem discr_compositum (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (hd : IsCoprime (discr K₁) (discr K₂)) :
    discr L = discr K₁ ^ finrank ℚ K₂ * discr K₂ ^ finrank ℚ K₁ := by
  have hL := natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow L K₁ K₂ h₁ h₂
    (isCoprime_differentIdeal_of_isCoprime_discr L hd)
  have hpar := neg_one_pow_nrComplexPlaces_compositum h₁ h₂
  calc discr L = (discr L).sign * (discr L).natAbs := (Int.sign_mul_natAbs _).symm
    _ = (-1) ^ nrComplexPlaces L *
          (((discr K₁).natAbs ^ finrank ℚ K₂ * (discr K₂).natAbs ^ finrank ℚ K₁ : ℕ) : ℤ) := by
        rw [sign_discr, hL]
    _ = ((-1) ^ nrComplexPlaces K₁ * ((discr K₁).natAbs : ℤ)) ^ finrank ℚ K₂ *
          ((-1) ^ nrComplexPlaces K₂ * ((discr K₂).natAbs : ℤ)) ^ finrank ℚ K₁ := by
        rw [hpar]
        push_cast
        ring
    _ = discr K₁ ^ finrank ℚ K₂ * discr K₂ ^ finrank ℚ K₁ := by
        rw [← sign_discr K₁, ← sign_discr K₂, Int.sign_mul_natAbs, Int.sign_mul_natAbs]

/-- **Instance-ready corollary of statement 4.** From the values of the sector discriminants and
degrees (with `Int.gcd d₁ d₂ = 1`, decidable by `norm_num`), the signed discriminant of the
compositum is `d₁ ^ n₂ * d₂ ^ n₁`. -/
theorem discr_compositum_eq (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    {d₁ d₂ : ℤ} {n₁ n₂ : ℕ} (hK₁ : discr K₁ = d₁) (hK₂ : discr K₂ = d₂)
    (hn₁ : finrank ℚ K₁ = n₁) (hn₂ : finrank ℚ K₂ = n₂) (hd : Int.gcd d₁ d₂ = 1) :
    discr L = d₁ ^ n₂ * d₂ ^ n₁ := by
  subst hK₁ hK₂ hn₁ hn₂
  exact discr_compositum h₁ h₂ (Int.isCoprime_iff_gcd_eq_one.2 hd)

/-- The numeral the instance will land on: `(-23)^4 * (-283)^3 = -6342648595267`. -/
theorem neg_twentythree_pow_four_mul_neg_283_pow_three :
    ((-23 : ℤ) ^ 4 * (-283) ^ 3) = -6342648595267 := by norm_num

end HermiteCompositum
