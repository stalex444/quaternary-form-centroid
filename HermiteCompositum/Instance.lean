module
public import Mathlib
public import HermiteCompositum.Defs
public import HermiteCompositum.Port014

@[expose] public section
/-!
# The degree-12 instance: `K = ℚ(ρ, Q)` as a tower, its integral structure, relative traces

The field is built as a tower
`K₃ = ℚ[X]/(X³ − X − 1)` and `L = K₃[Y]/(Y⁴ − Y − 1)`, with the two sectors as intermediate
fields `S₃ = ℚ⟮ρ⟯` and `S₄ = ℚ⟮Q⟯` of `L` (`ρ`, `Q` the images of the two roots).

Compared statements (numbering as in `Challenge.lean`):
* (7) `finrank ℚ S₃ = 3`, `finrank ℚ S₄ = 4`, `finrank ℚ L = 12`, `S₃.LinearDisjoint S₄`,
  `S₃ ⊔ S₄ = ⊤`.
* (8) `𝓞 S₃ = ℤ[ρ]`, `𝓞 S₄ = ℤ[Q]`, `discr S₃ = −23`, `discr S₄ = −283`, coprime, and
  `𝓞 L = ℤ[ρ, Q]` with ℤ-basis `{ρ^i Q^j}`.
* (9) `|discr L| = 23⁴ · 283³`; the signed value as corollaries of the sign inputs.
* (11) the relative traces on the product basis: `Tr_{L/S₃}(ρ^i Q^j) = s_j ρ^i`, `(s₀..s₃) =
  (4,0,0,3)`, and `Tr_{L/S₄}(ρ^i Q^j) = t_i Q^j`, `(t₀,t₁,t₂) = (3,0,2)`.
* (12) `Tr(−α⁻¹) = 1` for the two sector generators, hence the relative traces are split
  surjections onto the sector rings of integers, and `𝓞 L = (−Q⁻¹)·𝓞 S₃ ⊕ (𝓞 L ∩ ker Tr_{L/S₃})`
  of ranks `3 + 9` (likewise `(−ρ⁻¹)·𝓞 S₄ ⊕ (𝓞 L ∩ ker Tr_{L/S₄})`, ranks `4 + 8`). Bonus: the
  general-`n` theorem `Tr_{E/ℚ}(−α⁻¹) = 1` for `[E : ℚ] = n ≥ 2` and `αⁿ = α + 1`
  (`trace_neg_inv_of_pow_eq_add_one`), from which the two instances are re-derived.

The ℚ-level inputs (irreducibility, power sums, discriminants `−23`, `−283`) are the port
`HermiteCompositum.Port014` of the registered entry PALOMAR-2026-09-02-000014 (the polynomials
`fρ`, `fQ` and the irreducibility proofs now in `HermiteCompositum.Defs`).

Instance discipline: once `K₃` is a field, `Algebra ℚ K₃` resolves to `DivisionRing.toRatAlgebra`
while the ported lemmas (and Mathlib's `AdjoinRoot` API) use `AdjoinRoot.instAlgebra`. The two
are propositionally equal (`algebraRat_eq`) but not cheaply definitionally equal, so we never
state anything about `Algebra.trace ℚ K₃`; the ported facts reach the sectors only through the
`ℚ`-algebra equivalences `e₃ : AdjoinRoot fρ ≃ₐ[ℚ] S₃` and `e₄ : AdjoinRoot fQ ≃ₐ[ℚ] S₄`
built by `AdjoinRoot.equiv'`, whose source instance is fixed by the definition.
-/

open Polynomial NumberField NumberField.InfinitePlace IntermediateField Module

namespace HermiteCompositum.Instance

/-! ### A general lemma: irreducibility survives a coprime-degree base change -/

-- `irreducible_map_of_coprime_finrank`, `algebraRat_eq`, the tower `K₃`, `g`, `L` and its
-- instances, `ρ`, `Q`, `S₃`, `S₄`, `gen₃`, `gen₄`, `θ₃`, `θ₄`, `ρ'`, `Q'`, `T₃`, `T₄`, `σ₃`, `σ₄` and the
-- lemmas their bodies use are in `HermiteCompositum/Defs.lean` (shared verbatim with
-- `Challenge.lean`).

/-! ### The tower `ℚ ⊂ K₃ ⊂ L` -/

theorem g_eq : g = X ^ 4 - X - 1 := by
  simp [g, Port014.fQ, Polynomial.map_sub, Polynomial.map_pow]

theorem g_natDegree : g.natDegree = 4 := by
  rw [g, natDegree_map, Port014.fQ_natDegree]

theorem finrank_K₃_L : Module.finrank K₃ L = 4 := by
  rw [(AdjoinRoot.powerBasis' g_monic).finrank, AdjoinRoot.powerBasis'_dim, g_natDegree]

/-- Statement (7c): `[L : ℚ] = 12`. -/
theorem finrank_L : Module.finrank ℚ L = 12 := by
  rw [← Module.finrank_mul_finrank ℚ K₃ L, finrank_K₃, finrank_K₃_L]

theorem ρ_isIntegral : IsIntegral ℚ ρ :=
  ⟨Port014.fρ, Port014.fρ_monic, by rw [← aeval_def]; exact aeval_ρ⟩

theorem Q_isIntegral : IsIntegral ℚ Q :=
  ⟨Port014.fQ, Port014.fQ_monic, by rw [← aeval_def]; exact aeval_Q⟩

/-! ### The two sectors as intermediate fields of `L` -/

/-- Statement (7a): `[S₃ : ℚ] = 3`. -/
theorem finrank_S₃ : Module.finrank ℚ S₃ = 3 := by
  rw [S₃, adjoin.finrank ρ_isIntegral, minpoly_ρ, Port014.fρ_natDegree]

/-- Statement (7b): `[S₄ : ℚ] = 4`. -/
theorem finrank_S₄ : Module.finrank ℚ S₄ = 4 := by
  rw [S₄, adjoin.finrank Q_isIntegral, minpoly_Q, Port014.fQ_natDegree]

/-- Statement (7d): the sectors are linearly disjoint (degrees `3`, `4` coprime). -/
theorem S₃_linearDisjoint_S₄ : S₃.LinearDisjoint S₄ :=
  LinearDisjoint.of_finrank_coprime (by rw [finrank_S₃, finrank_S₄]; decide)

/-- Statement (7e): the sectors generate `L`. -/
theorem S₃_sup_S₄ : S₃ ⊔ S₄ = ⊤ := by
  apply eq_of_le_of_finrank_eq le_top
  rw [S₃_linearDisjoint_S₄.finrank_sup, finrank_S₃, finrank_S₄, finrank_top', finrank_L]

/-- Statement (7), bundled. -/
theorem setting :
    Module.finrank ℚ S₃ = 3 ∧ Module.finrank ℚ S₄ = 4 ∧ Module.finrank ℚ L = 12 ∧
      S₃.LinearDisjoint S₄ ∧ S₃ ⊔ S₄ = ⊤ :=
  ⟨finrank_S₃, finrank_S₄, finrank_L, S₃_linearDisjoint_S₄, S₃_sup_S₄⟩

/-! ### The sectors are the registered fields: `ℚ`-algebra equivalences -/

/-- The power basis of `S₃` with generator `gen₃`. -/
noncomputable def pb₃ : PowerBasis ℚ S₃ := adjoin.powerBasis ρ_isIntegral

/-- The power basis of `S₄` with generator `gen₄`. -/
noncomputable def pb₄ : PowerBasis ℚ S₄ := adjoin.powerBasis Q_isIntegral

theorem pb₃_gen : pb₃.gen = gen₃ := rfl

theorem pb₄_gen : pb₄.gen = gen₄ := rfl

/-- `AdjoinRoot (X³ − X − 1) ≃ₐ[ℚ] S₃`, root ↦ `gen₃`. The type is left to be inferred from
`AdjoinRoot.equiv'` on purpose: its source carries `AdjoinRoot.instAlgebra` (the instance of the
ported lemmas), not the `DivisionRing.toRatAlgebra` that an ascription would re-synthesize. -/
noncomputable def e₃ :=
  AdjoinRoot.equiv' Port014.fρ pb₃
    (by rw [pb₃_gen, minpoly_gen₃, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
    (by rw [pb₃_gen]; exact aeval_gen₃)

/-- `AdjoinRoot (X⁴ − X − 1) ≃ₐ[ℚ] S₄`, root ↦ `gen₄` (type inferred, as for `e₃`). -/
noncomputable def e₄ :=
  AdjoinRoot.equiv' Port014.fQ pb₄
    (by rw [pb₄_gen, minpoly_gen₄, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
    (by rw [pb₄_gen]; exact aeval_gen₄)

theorem e₃_root : e₃ (AdjoinRoot.root Port014.fρ) = gen₃ := by
  rw [e₃, AdjoinRoot.equiv'_apply]
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

theorem e₄_root : e₄ (AdjoinRoot.root Port014.fQ) = gen₄ := by
  rw [e₄, AdjoinRoot.equiv'_apply]
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

theorem e₃_comp_bρ : ⇑e₃ ∘ ⇑Port014.bρ = fun i : Fin 3 => gen₃ ^ (i : ℕ) := by
  funext i; simp [Port014.bρ_apply, map_pow, e₃_root]

theorem e₄_comp_bQ : ⇑e₄ ∘ ⇑Port014.bQ = fun i : Fin 4 => gen₄ ^ (i : ℕ) := by
  funext i; simp [Port014.bQ_apply, map_pow, e₄_root]

/-! ### Traces and discriminants of the sectors, transported from the port -/

/-- The power sums of `S₃`: `Tr_{S₃/ℚ}(gen₃^k) = (3, 0, 2, 3, 2)` for `k ≤ 4`. -/
theorem trace_gen₃_pow (k : ℕ) (hk : k ≤ 4) :
    Algebra.trace ℚ S₃ (gen₃ ^ k) = ![3, 0, 2, 3, 2] (⟨k, by omega⟩ : Fin 5) := by
  have h := Algebra.trace_eq_of_algEquiv e₃ (AdjoinRoot.root Port014.fρ ^ k)
  rw [map_pow, e₃_root, Port014.trace_rootρ_pow k hk] at h
  exact h

/-- The power sums of `S₄`: `Tr_{S₄/ℚ}(gen₄^k) = (4, 0, 0, 3, 4, 0, 3)` for `k ≤ 6`. -/
theorem trace_gen₄_pow (k : ℕ) (hk : k ≤ 6) :
    Algebra.trace ℚ S₄ (gen₄ ^ k) = ![4, 0, 0, 3, 4, 0, 3] (⟨k, by omega⟩ : Fin 7) := by
  have h := Algebra.trace_eq_of_algEquiv e₄ (AdjoinRoot.root Port014.fQ ^ k)
  rw [map_pow, e₄_root, Port014.trace_rootQ_pow k hk] at h
  exact h

/-- The `ℚ`-discriminant of the power basis `1, gen₃, gen₃²` of `S₃` is `−23`. -/
theorem discr_gen₃ : Algebra.discr ℚ (fun i : Fin 3 => gen₃ ^ (i : ℕ)) = -23 := by
  rw [← e₃_comp_bρ, ← Algebra.discr_eq_discr_of_algEquiv, Port014.discr_bρ]

/-- The `ℚ`-discriminant of the power basis `1, gen₄, gen₄², gen₄³` of `S₄` is `−283`. -/
theorem discr_gen₄ : Algebra.discr ℚ (fun i : Fin 4 => gen₄ ^ (i : ℕ)) = -283 := by
  rw [← e₄_comp_bQ, ← Algebra.discr_eq_discr_of_algEquiv, Port014.discr_bQ]

/-! ### Rings of integers: the squarefree-discriminant criterion -/

/-- The `ℤ`-discriminant of a family in `𝓞 K`, read in `ℚ`, is the `ℚ`-discriminant of the
family in `K`. -/
theorem discr_coe {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (v : ι → 𝓞 K) :
    ((Algebra.discr ℤ v : ℤ) : ℚ) = Algebra.discr ℚ (fun i => algebraMap (𝓞 K) K (v i)) := by
  rw [Algebra.discr_def, Algebra.discr_def]
  have : ((Algebra.traceMatrix ℤ v).det : ℚ)
      = ((algebraMap ℤ ℚ).mapMatrix (Algebra.traceMatrix ℤ v)).det :=
    RingHom.map_det (algebraMap ℤ ℚ) _
  rw [this]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
    Algebra.traceForm_apply, ← map_mul]
  exact (Algebra.trace_localization ℤ (nonZeroDivisors ℤ) (v i * v j)).symm

/-- **Squarefree discriminant ⇒ basis** (Marcus, Ex. 2.27(e); duplicated from
`Squarefree.lean` so that this file is self-contained). Over a commutative ring `A`, if `B` has
an `A`-basis indexed by `ι` and `v : ι → B` has squarefree discriminant, then `v` is a basis. -/
theorem isBasis_of_squarefree_discr {A B ι : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Fintype ι] [DecidableEq ι] (b : Basis ι A B) (v : ι → B)
    (hv : Squarefree (Algebra.discr A v)) :
    LinearIndependent A v ∧ Submodule.span A (Set.range v) = ⊤ := by
  rw [b.is_basis_iff_det, b.det_apply]
  have h := Algebra.discr_of_matrix_vecMul (A := A) (⇑b) (b.toMatrix v)
  rw [b.toMatrix_map_vecMul] at h
  rw [h] at hv
  exact hv _ ⟨Algebra.discr A ⇑b, by ring⟩

/-- Number-field form: `[K:ℚ]` algebraic integers with squarefree discriminant span `𝓞 K`. -/
theorem span_eq_top_of_squarefree_discr {K ι : Type*} [Field K] [NumberField K]
    [Fintype ι] [DecidableEq ι] (v : ι → 𝓞 K)
    (hcard : Fintype.card ι = finrank ℚ K) (hv : Squarefree (Algebra.discr ℤ v)) :
    Submodule.span ℤ (Set.range v) = ⊤ := by
  let b₀ := NumberField.RingOfIntegers.basis K
  have e : Free.ChooseBasisIndex ℤ (𝓞 K) ≃ ι := by
    refine Fintype.equivOfCardEq ?_
    rw [hcard, ← NumberField.RingOfIntegers.rank, finrank_eq_card_chooseBasisIndex]
  exact (isBasis_of_squarefree_discr (b₀.reindex e) v hv).2

/-- A `ℤ`-basis of `𝓞 K` from a family of the right size with squarefree discriminant. -/
theorem linearIndependent_of_squarefree_discr {K ι : Type*} [Field K] [NumberField K]
    [Fintype ι] [DecidableEq ι] (v : ι → 𝓞 K)
    (hcard : Fintype.card ι = finrank ℚ K) (hv : Squarefree (Algebra.discr ℤ v)) :
    LinearIndependent ℤ v := by
  let b₀ := NumberField.RingOfIntegers.basis K
  have e : Free.ChooseBasisIndex ℤ (𝓞 K) ≃ ι := by
    refine Fintype.equivOfCardEq ?_
    rw [hcard, ← NumberField.RingOfIntegers.rank, finrank_eq_card_chooseBasisIndex]
  exact (isBasis_of_squarefree_discr (b₀.reindex e) v hv).1

/-- A `ℤ`-basis of `𝓞 K` from a family of the right size with squarefree discriminant. -/
noncomputable def basisOfSquarefreeDiscr {K ι : Type*} [Field K] [NumberField K]
    [Fintype ι] [DecidableEq ι] (v : ι → 𝓞 K)
    (hcard : Fintype.card ι = finrank ℚ K) (hv : Squarefree (Algebra.discr ℤ v)) :
    Basis ι ℤ (𝓞 K) :=
  Basis.mk (linearIndependent_of_squarefree_discr v hcard hv)
    (by rw [span_eq_top_of_squarefree_discr v hcard hv])

@[simp] theorem basisOfSquarefreeDiscr_apply {K ι : Type*} [Field K] [NumberField K]
    [Fintype ι] [DecidableEq ι] (v : ι → 𝓞 K)
    (hcard : Fintype.card ι = finrank ℚ K) (hv : Squarefree (Algebra.discr ℤ v)) (i : ι) :
    basisOfSquarefreeDiscr v hcard hv i = v i := by
  simp [basisOfSquarefreeDiscr]

/-- Monogenic form: `θ ∈ 𝓞 K` whose powers have squarefree discriminant generates `𝓞 K`. -/
theorem adjoin_eq_top_of_squarefree_discr {K : Type*} [Field K] [NumberField K]
    (θ : 𝓞 K)
    (hv : Squarefree (Algebra.discr ℤ (fun i : Fin (finrank ℚ K) => θ ^ (i : ℕ)))) :
    Algebra.adjoin ℤ {θ} = ⊤ := by
  have hspan := span_eq_top_of_squarefree_discr
    (fun i : Fin (finrank ℚ K) => θ ^ (i : ℕ)) (Fintype.card_fin _) hv
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Submodule.span ℤ (Set.range fun i : Fin (finrank ℚ K) => θ ^ (i : ℕ)) := by
    rw [hspan]; trivial
  refine (Submodule.span_le (p := Subalgebra.toSubmodule (Algebra.adjoin ℤ {θ}))).mpr ?_ hx
  rintro _ ⟨i, rfl⟩
  exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton θ)) _

/-! ### Statement (8): the sector rings of integers -/

@[simp] theorem coe_θ₃ : algebraMap (𝓞 S₃) S₃ θ₃ = gen₃ := rfl

@[simp] theorem coe_θ₄ : algebraMap (𝓞 S₄) S₄ θ₄ = gen₄ := rfl

/-- The `ℤ`-discriminant of `1, θ₃, θ₃²` in `𝓞 S₃` is `−23`. -/
theorem discr_θ₃ : Algebra.discr ℤ (fun i : Fin 3 => θ₃ ^ (i : ℕ)) = -23 := by
  have h := discr_coe (fun i : Fin 3 => θ₃ ^ (i : ℕ))
  simp only [map_pow, coe_θ₃] at h
  rw [discr_gen₃] at h
  exact_mod_cast h

/-- The `ℤ`-discriminant of `1, θ₄, θ₄², θ₄³` in `𝓞 S₄` is `−283`. -/
theorem discr_θ₄ : Algebra.discr ℤ (fun i : Fin 4 => θ₄ ^ (i : ℕ)) = -283 := by
  have h := discr_coe (fun i : Fin 4 => θ₄ ^ (i : ℕ))
  simp only [map_pow, coe_θ₄] at h
  rw [discr_gen₄] at h
  exact_mod_cast h

theorem squarefree_neg23 : Squarefree (-23 : ℤ) :=
  (Int.prime_iff_natAbs_prime.mpr (by norm_num)).squarefree

theorem squarefree_neg283 : Squarefree (-283 : ℤ) :=
  (Int.prime_iff_natAbs_prime.mpr (by norm_num)).squarefree

/-- The `ℤ`-basis `1, θ₃, θ₃²` of `𝓞 S₃`. -/
noncomputable def b₃ : Basis (Fin 3) ℤ (𝓞 S₃) :=
  basisOfSquarefreeDiscr (fun i : Fin 3 => θ₃ ^ (i : ℕ))
    (by rw [Fintype.card_fin, finrank_S₃]) (by rw [discr_θ₃]; exact squarefree_neg23)

/-- The `ℤ`-basis `1, θ₄, θ₄², θ₄³` of `𝓞 S₄`. -/
noncomputable def b₄ : Basis (Fin 4) ℤ (𝓞 S₄) :=
  basisOfSquarefreeDiscr (fun i : Fin 4 => θ₄ ^ (i : ℕ))
    (by rw [Fintype.card_fin, finrank_S₄]) (by rw [discr_θ₄]; exact squarefree_neg283)

theorem b₃_apply (i : Fin 3) : b₃ i = θ₃ ^ (i : ℕ) := by simp [b₃]

theorem b₄_apply (i : Fin 4) : b₄ i = θ₄ ^ (i : ℕ) := by simp [b₄]

/-- Statement (8a): `𝓞 S₃ = ℤ[ρ]`. -/
theorem adjoin_θ₃ : Algebra.adjoin ℤ {θ₃} = ⊤ := by
  apply adjoin_eq_top_of_squarefree_discr
  rw [finrank_S₃, discr_θ₃]; exact squarefree_neg23

/-- Statement (8b): `𝓞 S₄ = ℤ[Q]`. -/
theorem adjoin_θ₄ : Algebra.adjoin ℤ {θ₄} = ⊤ := by
  apply adjoin_eq_top_of_squarefree_discr
  rw [finrank_S₄, discr_θ₄]; exact squarefree_neg283

/-- Statement (8c): `discr S₃ = −23`. -/
theorem discr_S₃ : discr S₃ = -23 := by
  rw [← discr_eq_discr S₃ b₃]
  have : ⇑b₃ = fun i : Fin 3 => θ₃ ^ (i : ℕ) := funext b₃_apply
  rw [this, discr_θ₃]

/-- Statement (8d): `discr S₄ = −283`. -/
theorem discr_S₄ : discr S₄ = -283 := by
  rw [← discr_eq_discr S₄ b₄]
  have : ⇑b₄ = fun i : Fin 4 => θ₄ ^ (i : ℕ) := funext b₄_apply
  rw [this, discr_θ₄]

/-- Statement (8e): the sector discriminants are coprime. -/
theorem isCoprime_discr : IsCoprime (discr S₃) (discr S₄) := by
  rw [discr_S₃, discr_S₄, Int.isCoprime_iff_gcd_eq_one]; decide

/-! ### Statement (8f): `𝓞 L = ℤ[ρ, Q]` -/

@[simp] theorem coe_ρ' : algebraMap (𝓞 L) L ρ' = ρ := rfl

@[simp] theorem coe_Q' : algebraMap (𝓞 L) L Q' = Q := rfl

theorem algebraMap_θ₃ : algebraMap (𝓞 S₃) (𝓞 L) θ₃ = ρ' := by
  apply RingOfIntegers.ext
  show algebraMap S₃ L gen₃ = ρ
  exact algebraMap_gen₃

theorem algebraMap_θ₄ : algebraMap (𝓞 S₄) (𝓞 L) θ₄ = Q' := by
  apply RingOfIntegers.ext
  show algebraMap S₄ L gen₄ = Q
  exact algebraMap_gen₄

theorem isCoprime_differentIdeal :
    IsCoprime ((differentIdeal ℤ (𝓞 S₃)).map (algebraMap (𝓞 S₃) (𝓞 L)))
      ((differentIdeal ℤ (𝓞 S₄)).map (algebraMap (𝓞 S₄) (𝓞 L))) :=
  isCoprime_differentIdeal_of_isCoprime_discr L isCoprime_discr

theorem S₃_sup_S₄_toSubalgebra : S₃.toSubalgebra ⊔ S₄.toSubalgebra = ⊤ := by
  simp [← sup_toSubalgebra_of_left, S₃_sup_S₄]

/-- Statement (8f): `𝓞 L = ℤ[ρ, Q]` (Mathlib's coprime-compositum theorem applied to the two
monogenic sectors). -/
theorem adjoin_ρ'_Q' : Algebra.adjoin ℤ {ρ', Q'} = ⊤ := by
  have := IsDedekindDomain.adjoin_union_eq_top_of_isCoprime_differentialIdeal ℤ (𝓞 L)
    (𝓞 S₃) (𝓞 S₄) S₃_linearDisjoint_S₄ S₃_sup_S₄_toSubalgebra isCoprime_differentIdeal
    adjoin_θ₃ adjoin_θ₄
  rwa [Set.image_singleton, Set.image_singleton, Set.singleton_union, algebraMap_θ₃,
    algebraMap_θ₄] at this

/-- The `ℤ`-basis `{ρ^i Q^j : i < 3, j < 4}` of `𝓞 L` (the lift of the `ℤ`-basis of `𝓞 S₄` to
an `𝓞 S₃`-basis of `𝓞 L`, then the tower basis over `ℤ`). -/
noncomputable def bL : Basis (Fin 3 × Fin 4) ℤ (𝓞 L) :=
  b₃.smulTower (b₄.ofIsCoprimeDifferentIdeal ℤ (𝓞 L) (𝓞 S₃) (𝓞 S₄) S₃_linearDisjoint_S₄
    S₃_sup_S₄_toSubalgebra isCoprime_differentIdeal)

/-- Statement (8g): the basis elements are the monomials `ρ^i Q^j`. -/
theorem bL_apply (p : Fin 3 × Fin 4) : bL p = ρ' ^ (p.1 : ℕ) * Q' ^ (p.2 : ℕ) := by
  rw [bL, Basis.smulTower_apply, Module.Basis.ofIsCoprimeDifferentIdeal_apply, b₃_apply,
    b₄_apply, Algebra.smul_def, map_pow, map_pow, algebraMap_θ₃, algebraMap_θ₄]

/-! ### Statement (9): the discriminant of `L` -/

/-- Statement (9): `|discr L| = 23⁴ · 283³` (Mathlib's compositum theorem for coprime
discriminants). -/
theorem natAbs_discr_L : (discr L).natAbs = 23 ^ 4 * 283 ^ 3 := by
  have h := natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow L S₃ S₄
    S₃_linearDisjoint_S₄ S₃_sup_S₄ isCoprime_differentIdeal
  rw [h, discr_S₃, discr_S₄, finrank_S₃, finrank_S₄]
  rfl

/-- The signed value, given the signed compositum identity (statement 4, `Places`) as a
hypothesis. -/
theorem discr_L_of_signed_compositum
    (h : discr L = discr S₃ ^ Module.finrank ℚ S₄ * discr S₄ ^ Module.finrank ℚ S₃) :
    discr L = (-23) ^ 4 * (-283) ^ 3 := by
  rw [h, discr_S₃, discr_S₄, finrank_S₃, finrank_S₄]

/-- The signed value, given `r₂(L) = 5` (`Places`) as a hypothesis, via `sign_discr`. -/
theorem discr_L_of_nrComplexPlaces (h : nrComplexPlaces L = 5) :
    discr L = -(23 ^ 4 * 283 ^ 3) := by
  have hs := sign_discr L
  rw [h] at hs
  have := Int.sign_mul_natAbs (discr L)
  rw [hs, natAbs_discr_L] at this
  rw [← this]; norm_num

/-! ### Statement (11): the relative traces on the product basis `ρ^i Q^j` -/

theorem ρ_pow_eq (i : ℕ) : ρ ^ i = algebraMap S₃ L (gen₃ ^ i) := by
  rw [map_pow, algebraMap_gen₃]

theorem Q_pow_eq (j : ℕ) : Q ^ j = algebraMap S₄ L (gen₄ ^ j) := by
  rw [map_pow, algebraMap_gen₄]

theorem S₄_linearDisjoint_S₃ : S₄.LinearDisjoint S₃ := S₃_linearDisjoint_S₄.symm

theorem S₄_sup_S₃ : S₄ ⊔ S₃ = ⊤ := by rw [sup_comm]; exact S₃_sup_S₄

/-- `Tr_{L/S₃}(Q^j) = s_j` with `(s₀, s₁, s₂, s₃) = (4, 0, 0, 3)` (the power sums of the
quartic): the relative trace to the cubic sector is `id ⊗ Tr_{S₄/ℚ}`. -/
theorem trace_S₃_Q_pow (j : Fin 4) :
    Algebra.trace S₃ L (Q ^ (j : ℕ)) = algebraMap ℚ S₃ (![4, 0, 0, 3] j) := by
  rw [Q_pow_eq, S₃_linearDisjoint_S₄.trace_algebraMap S₃_sup_S₄, trace_gen₄_pow j (by omega)]
  fin_cases j <;> rfl

/-- `Tr_{L/S₄}(ρ^i) = t_i` with `(t₀, t₁, t₂) = (3, 0, 2)` (the power sums of the cubic): the
relative trace to the quartic sector is `Tr_{S₃/ℚ} ⊗ id`. -/
theorem trace_S₄_ρ_pow (i : Fin 3) :
    Algebra.trace S₄ L (ρ ^ (i : ℕ)) = algebraMap ℚ S₄ (![3, 0, 2] i) := by
  rw [ρ_pow_eq, S₄_linearDisjoint_S₃.trace_algebraMap S₄_sup_S₃, trace_gen₃_pow i (by omega)]
  fin_cases i <;> rfl

/-- Statement (11a): `Tr_{L/S₃}(ρ^i Q^j) = s_j · ρ^i`. -/
theorem trace_S₃_basis (i : ℕ) (j : Fin 4) :
    Algebra.trace S₃ L (ρ ^ i * Q ^ (j : ℕ)) = algebraMap ℚ S₃ (![4, 0, 0, 3] j) * gen₃ ^ i := by
  rw [ρ_pow_eq, ← Algebra.smul_def, map_smul, trace_S₃_Q_pow, smul_eq_mul, mul_comm]

/-- Statement (11b): `Tr_{L/S₄}(ρ^i Q^j) = t_i · Q^j`. -/
theorem trace_S₄_basis (i : Fin 3) (j : ℕ) :
    Algebra.trace S₄ L (ρ ^ (i : ℕ) * Q ^ j) = algebraMap ℚ S₄ (![3, 0, 2] i) * gen₄ ^ j := by
  rw [mul_comm, Q_pow_eq, ← Algebra.smul_def, map_smul, trace_S₄_ρ_pow, smul_eq_mul, mul_comm]

/-! ### Statement (12): unit sections `−α⁻¹` and surjectivity on the rings of integers -/

theorem gen₃_pow_three : gen₃ ^ 3 = gen₃ + 1 := by
  have h := aeval_gen₃
  simp only [Port014.fρ, map_sub, map_pow, map_one, aeval_X] at h
  linear_combination h

theorem gen₄_pow_four : gen₄ ^ 4 = gen₄ + 1 := by
  have h := aeval_gen₄
  simp only [Port014.fQ, map_sub, map_pow, map_one, aeval_X] at h
  linear_combination h

/-- `−ρ⁻¹ = 1 − ρ²` (a unit of `ℤ[ρ]`). -/
theorem neg_inv_gen₃ : -gen₃⁻¹ = 1 - gen₃ ^ 2 := by
  have h : gen₃⁻¹ = gen₃ ^ 2 - 1 := by
    apply inv_eq_of_mul_eq_one_right
    linear_combination gen₃_pow_three
  rw [h, neg_sub]

/-- `−Q⁻¹ = 1 − Q³` (a unit of `ℤ[Q]`). -/
theorem neg_inv_gen₄ : -gen₄⁻¹ = 1 - gen₄ ^ 3 := by
  have h : gen₄⁻¹ = gen₄ ^ 3 - 1 := by
    apply inv_eq_of_mul_eq_one_right
    linear_combination gen₄_pow_four
  rw [h, neg_sub]

/-- Statement (12a), `n = 3`: `Tr_{ℚ(ρ)/ℚ}(−ρ⁻¹) = 1`. -/
theorem trace_neg_inv_gen₃ : Algebra.trace ℚ S₃ (-gen₃⁻¹) = 1 := by
  have h0 : Algebra.trace ℚ S₃ 1 = 3 := by
    have := trace_gen₃_pow 0 (by norm_num); rw [pow_zero] at this; simpa using this
  have h2 : Algebra.trace ℚ S₃ (gen₃ ^ 2) = 2 := by
    have := trace_gen₃_pow 2 (by norm_num); simpa using this
  rw [neg_inv_gen₃, map_sub, h0, h2]; norm_num

/-- Statement (12a), `n = 4`: `Tr_{ℚ(Q)/ℚ}(−Q⁻¹) = 1`. -/
theorem trace_neg_inv_gen₄ : Algebra.trace ℚ S₄ (-gen₄⁻¹) = 1 := by
  have h0 : Algebra.trace ℚ S₄ 1 = 4 := by
    have := trace_gen₄_pow 0 (by norm_num); rw [pow_zero] at this; simpa using this
  have h3 : Algebra.trace ℚ S₄ (gen₄ ^ 3) = 3 := by
    have := trace_gen₄_pow 3 (by norm_num); simpa using this
  rw [neg_inv_gen₄, map_sub, h0, h3]; norm_num

theorem neg_inv_Q : -Q⁻¹ = 1 - Q ^ 3 := by
  rw [← algebraMap_gen₄, ← map_pow, ← map_inv₀, ← map_neg, ← map_one (algebraMap S₄ L),
    ← map_sub, neg_inv_gen₄]

theorem neg_inv_ρ : -ρ⁻¹ = 1 - ρ ^ 2 := by
  rw [← algebraMap_gen₃, ← map_pow, ← map_inv₀, ← map_neg, ← map_one (algebraMap S₃ L),
    ← map_sub, neg_inv_gen₃]

/-- `Tr_{L/S₃}(−Q⁻¹) = 1`. -/
theorem trace_S₃_neg_inv_Q : Algebra.trace S₃ L (-Q⁻¹) = 1 := by
  have h0 : Algebra.trace S₃ L 1 = algebraMap ℚ S₃ 4 := by
    have := trace_S₃_Q_pow 0
    rwa [Fin.val_zero, pow_zero] at this
  have h3 : Algebra.trace S₃ L (Q ^ 3) = algebraMap ℚ S₃ 3 := trace_S₃_Q_pow 3
  rw [neg_inv_Q, map_sub, h0, h3, ← map_sub]
  norm_num

/-- `Tr_{L/S₄}(−ρ⁻¹) = 1`. -/
theorem trace_S₄_neg_inv_ρ : Algebra.trace S₄ L (-ρ⁻¹) = 1 := by
  have h0 : Algebra.trace S₄ L 1 = algebraMap ℚ S₄ 3 := by
    have := trace_S₄_ρ_pow 0
    rwa [Fin.val_zero, pow_zero] at this
  have h2 : Algebra.trace S₄ L (ρ ^ 2) = algebraMap ℚ S₄ 2 := trace_S₄_ρ_pow 2
  rw [neg_inv_ρ, map_sub, h0, h2, ← map_sub]
  norm_num

/-- Statement (12b): `Tr_{L/S₃}(−Q⁻¹ · a) = a` for all `a ∈ S₃`. -/
theorem trace_S₃_neg_inv_Q_mul (a : S₃) : Algebra.trace S₃ L (-Q⁻¹ * algebraMap S₃ L a) = a := by
  rw [mul_comm, ← Algebra.smul_def, map_smul, trace_S₃_neg_inv_Q, smul_eq_mul, mul_one]

/-- Statement (12b): `Tr_{L/S₄}(−ρ⁻¹ · b) = b` for all `b ∈ S₄`. -/
theorem trace_S₄_neg_inv_ρ_mul (b : S₄) : Algebra.trace S₄ L (-ρ⁻¹ * algebraMap S₄ L b) = b := by
  rw [mul_comm, ← Algebra.smul_def, map_smul, trace_S₄_neg_inv_ρ, smul_eq_mul, mul_one]

/-- Statement (12c): `Tr_{L/S₃}` maps `𝓞 L` ONTO `𝓞 S₃` — every `b ∈ 𝓞 S₃` is the trace of
`(1 − Q³) · b ∈ 𝓞 L`. -/
theorem trace_S₃_surjective (b : 𝓞 S₃) :
    ∃ x : 𝓞 L, Algebra.trace S₃ L (algebraMap (𝓞 L) L x) = algebraMap (𝓞 S₃) S₃ b := by
  refine ⟨(1 - Q' ^ 3) * algebraMap (𝓞 S₃) (𝓞 L) b, ?_⟩
  have hx : algebraMap (𝓞 L) L ((1 - Q' ^ 3) * algebraMap (𝓞 S₃) (𝓞 L) b)
      = -Q⁻¹ * algebraMap S₃ L (algebraMap (𝓞 S₃) S₃ b) := by
    rw [map_mul, map_sub, map_one, map_pow, coe_Q', neg_inv_Q, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 S₃) S₃ L]
  rw [hx, trace_S₃_neg_inv_Q_mul]

/-- Statement (12c): `Tr_{L/S₄}` maps `𝓞 L` ONTO `𝓞 S₄`. -/
theorem trace_S₄_surjective (b : 𝓞 S₄) :
    ∃ x : 𝓞 L, Algebra.trace S₄ L (algebraMap (𝓞 L) L x) = algebraMap (𝓞 S₄) S₄ b := by
  refine ⟨(1 - ρ' ^ 2) * algebraMap (𝓞 S₄) (𝓞 L) b, ?_⟩
  have hx : algebraMap (𝓞 L) L ((1 - ρ' ^ 2) * algebraMap (𝓞 S₄) (𝓞 L) b)
      = -ρ⁻¹ * algebraMap S₄ L (algebraMap (𝓞 S₄) S₄ b) := by
    rw [map_mul, map_sub, map_one, map_pow, coe_ρ', neg_inv_ρ, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 S₄) S₄ L]
  rw [hx, trace_S₄_neg_inv_ρ_mul]

/-! ### Statement (12d): `𝓞 L = (−Q⁻¹)·𝓞 S₃ ⊕ (𝓞 L ∩ ker Tr_{L/S₃})`, of ranks `3 + 9`
(and `𝓞 L = (−ρ⁻¹)·𝓞 S₄ ⊕ (𝓞 L ∩ ker Tr_{L/S₄})`, of ranks `4 + 8`).

The two summands are `ℤ`-submodules of `𝓞 L`: the image of the section `σ₃ : b ↦ −Q⁻¹·b` and
the kernel of the integral relative trace `T₃`. The decomposition is `IsCompl (range σ₃)
(ker T₃)` (internal direct sum), and the ranks are `Module.finrank ℤ`. -/

@[simp] theorem coe_T₃ (x : 𝓞 L) :
    algebraMap (𝓞 S₃) S₃ (T₃ x) = Algebra.trace S₃ L (algebraMap (𝓞 L) L x) := rfl

@[simp] theorem coe_T₄ (x : 𝓞 L) :
    algebraMap (𝓞 S₄) S₄ (T₄ x) = Algebra.trace S₄ L (algebraMap (𝓞 L) L x) := rfl

/-- `ker T₃` is `𝓞 L ∩ ker Tr_{L/S₃}`. -/
theorem mem_ker_T₃ (x : 𝓞 L) :
    x ∈ LinearMap.ker T₃ ↔ Algebra.trace S₃ L (algebraMap (𝓞 L) L x) = 0 := by
  rw [LinearMap.mem_ker, ← RingOfIntegers.eq_iff]
  exact Iff.rfl

/-- `ker T₄` is `𝓞 L ∩ ker Tr_{L/S₄}`. -/
theorem mem_ker_T₄ (x : 𝓞 L) :
    x ∈ LinearMap.ker T₄ ↔ Algebra.trace S₄ L (algebraMap (𝓞 L) L x) = 0 := by
  rw [LinearMap.mem_ker, ← RingOfIntegers.eq_iff]
  exact Iff.rfl

theorem σ₃_apply (b : 𝓞 S₃) : σ₃ b = (1 - Q' ^ 3) * algebraMap (𝓞 S₃) (𝓞 L) b := rfl

theorem σ₄_apply (b : 𝓞 S₄) : σ₄ b = (1 - ρ' ^ 2) * algebraMap (𝓞 S₄) (𝓞 L) b := rfl

/-- `σ₃ b` is `−Q⁻¹ · b` in `L`. -/
theorem coe_σ₃ (b : 𝓞 S₃) :
    algebraMap (𝓞 L) L (σ₃ b) = -Q⁻¹ * algebraMap S₃ L (algebraMap (𝓞 S₃) S₃ b) := by
  rw [σ₃_apply, map_mul, map_sub, map_one, map_pow, coe_Q', neg_inv_Q,
    ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 S₃) S₃ L]

/-- `σ₄ b` is `−ρ⁻¹ · b` in `L`. -/
theorem coe_σ₄ (b : 𝓞 S₄) :
    algebraMap (𝓞 L) L (σ₄ b) = -ρ⁻¹ * algebraMap S₄ L (algebraMap (𝓞 S₄) S₄ b) := by
  rw [σ₄_apply, map_mul, map_sub, map_one, map_pow, coe_ρ', neg_inv_ρ,
    ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 S₄) S₄ L]

/-- `T₃ ∘ σ₃ = id`: the integral relative trace splits. -/
theorem T₃_σ₃ (b : 𝓞 S₃) : T₃ (σ₃ b) = b := by
  apply RingOfIntegers.ext
  show Algebra.trace S₃ L (algebraMap (𝓞 L) L (σ₃ b)) = algebraMap (𝓞 S₃) S₃ b
  rw [coe_σ₃, trace_S₃_neg_inv_Q_mul]

/-- `T₄ ∘ σ₄ = id`: the integral relative trace splits. -/
theorem T₄_σ₄ (b : 𝓞 S₄) : T₄ (σ₄ b) = b := by
  apply RingOfIntegers.ext
  show Algebra.trace S₄ L (algebraMap (𝓞 L) L (σ₄ b)) = algebraMap (𝓞 S₄) S₄ b
  rw [coe_σ₄, trace_S₄_neg_inv_ρ_mul]

theorem σ₃_injective : Function.Injective σ₃ := Function.LeftInverse.injective T₃_σ₃

theorem σ₄_injective : Function.Injective σ₄ := Function.LeftInverse.injective T₄_σ₄

/-- Statement (12c) in linear-map form: `T₃ : 𝓞 L → 𝓞 S₃` is surjective. -/
theorem T₃_surjective : Function.Surjective T₃ := Function.LeftInverse.surjective T₃_σ₃

/-- Statement (12c) in linear-map form: `T₄ : 𝓞 L → 𝓞 S₄` is surjective. -/
theorem T₄_surjective : Function.Surjective T₄ := Function.LeftInverse.surjective T₄_σ₄

/-- `𝓞 L = (−Q⁻¹)·𝓞 S₃ ⊕ (𝓞 L ∩ ker Tr_{L/S₃})` as an internal direct sum of `ℤ`-modules. -/
theorem isCompl_range_σ₃_ker_T₃ : IsCompl (LinearMap.range σ₃) (LinearMap.ker T₃) := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro x ⟨b, rfl⟩ hx
    rw [LinearMap.mem_ker, T₃_σ₃] at hx
    rw [hx, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    rw [Submodule.mem_sup]
    refine ⟨σ₃ (T₃ x), ⟨T₃ x, rfl⟩, x - σ₃ (T₃ x), ?_, add_sub_cancel _ _⟩
    rw [LinearMap.mem_ker, map_sub, T₃_σ₃, sub_self]

/-- `𝓞 L = (−ρ⁻¹)·𝓞 S₄ ⊕ (𝓞 L ∩ ker Tr_{L/S₄})` as an internal direct sum of `ℤ`-modules. -/
theorem isCompl_range_σ₄_ker_T₄ : IsCompl (LinearMap.range σ₄) (LinearMap.ker T₄) := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro x ⟨b, rfl⟩ hx
    rw [LinearMap.mem_ker, T₄_σ₄] at hx
    rw [hx, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    rw [Submodule.mem_sup]
    refine ⟨σ₄ (T₄ x), ⟨T₄ x, rfl⟩, x - σ₄ (T₄ x), ?_, add_sub_cancel _ _⟩
    rw [LinearMap.mem_ker, map_sub, T₄_σ₄, sub_self]

theorem finrank_int_S₃ : Module.finrank ℤ (𝓞 S₃) = 3 := by
  rw [RingOfIntegers.rank, finrank_S₃]

theorem finrank_int_S₄ : Module.finrank ℤ (𝓞 S₄) = 4 := by
  rw [RingOfIntegers.rank, finrank_S₄]

theorem finrank_int_L : Module.finrank ℤ (𝓞 L) = 12 := by
  rw [RingOfIntegers.rank, finrank_L]

/-- The summand `(−Q⁻¹)·𝓞 S₃` has rank `3`. -/
theorem finrank_range_σ₃ : Module.finrank ℤ (LinearMap.range σ₃) = 3 := by
  rw [← (LinearEquiv.ofInjective σ₃ σ₃_injective).finrank_eq, finrank_int_S₃]

/-- The summand `(−ρ⁻¹)·𝓞 S₄` has rank `4`. -/
theorem finrank_range_σ₄ : Module.finrank ℤ (LinearMap.range σ₄) = 4 := by
  rw [← (LinearEquiv.ofInjective σ₄ σ₄_injective).finrank_eq, finrank_int_S₄]

/-- The summand `𝓞 L ∩ ker Tr_{L/S₃}` has rank `9` (rank–nullity over `ℤ`). -/
theorem finrank_ker_T₃ : Module.finrank ℤ (LinearMap.ker T₃) = 9 := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.ker T₃)
  rw [(T₃.quotKerEquivOfSurjective T₃_surjective).finrank_eq, finrank_int_S₃, finrank_int_L] at h
  omega

/-- The summand `𝓞 L ∩ ker Tr_{L/S₄}` has rank `8` (rank–nullity over `ℤ`). -/
theorem finrank_ker_T₄ : Module.finrank ℤ (LinearMap.ker T₄) = 8 := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.ker T₄)
  rw [(T₄.quotKerEquivOfSurjective T₄_surjective).finrank_eq, finrank_int_S₄, finrank_int_L] at h
  omega

/-- Statement (12d), bundled: `𝓞 L = (−Q⁻¹)·𝓞 S₃ ⊕ (𝓞 L ∩ ker Tr_{L/S₃})` of ranks `3 + 9`. -/
theorem decomposition_S₃ :
    IsCompl (LinearMap.range σ₃) (LinearMap.ker T₃) ∧
      Module.finrank ℤ (LinearMap.range σ₃) = 3 ∧ Module.finrank ℤ (LinearMap.ker T₃) = 9 :=
  ⟨isCompl_range_σ₃_ker_T₃, finrank_range_σ₃, finrank_ker_T₃⟩

/-- Statement (12d), bundled: `𝓞 L = (−ρ⁻¹)·𝓞 S₄ ⊕ (𝓞 L ∩ ker Tr_{L/S₄})` of ranks `4 + 8`. -/
theorem decomposition_S₄ :
    IsCompl (LinearMap.range σ₄) (LinearMap.ker T₄) ∧
      Module.finrank ℤ (LinearMap.range σ₄) = 4 ∧ Module.finrank ℤ (LinearMap.ker T₄) = 8 :=
  ⟨isCompl_range_σ₄_ker_T₄, finrank_range_σ₄, finrank_ker_T₄⟩

/-! ### Statement (12a) for general `n` (bonus): `Tr_{ℚ(α)/ℚ}(−α⁻¹) = 1` for a root `α` of
`xⁿ − x − 1`, `n ≥ 2`.

`β = −α⁻¹` is a root of the monic polynomial `xⁿ − xⁿ⁻¹ − (−1)ⁿ`. Since `ℚ(β) = ℚ(α)` has
degree `n` (Selmer: `xⁿ − x − 1` is irreducible over `ℚ`), that polynomial IS the minimal
polynomial of `β` by degree count alone — no irreducibility of the reversed polynomial is used —
and the trace is minus its next coefficient, `1`. -/

/-- **Statement (12a), general `n`.** Let `E/ℚ` have degree `n ≥ 2` and let `α ∈ E` satisfy
`αⁿ = α + 1`. Then `Tr_{E/ℚ}(−α⁻¹) = 1`. (The hypothesis `[E : ℚ] = n` says `E = ℚ(α)`.) -/
theorem trace_neg_inv_of_pow_eq_add_one {E : Type*} [Field E] [Algebra ℚ E]
    [FiniteDimensional ℚ E] {n : ℕ} (hn : 2 ≤ n) (hE : Module.finrank ℚ E = n) {α : E}
    (hα : α ^ n = α + 1) : Algebra.trace ℚ E (-α⁻¹) = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega), zero_add] at hα
    exact zero_ne_one hα
  obtain ⟨β, hβ⟩ : ∃ β : E, β = -α⁻¹ := ⟨_, rfl⟩
  rw [← hβ]
  have hβ0 : β ≠ 0 := by rw [hβ]; exact neg_ne_zero.mpr (inv_ne_zero hα0)
  have hαβ : α = -β⁻¹ := by rw [hβ, inv_neg, inv_inv, neg_neg]
  -- the Selmer polynomial is the minimal polynomial of `α`, so `ℚ⟮α⟯ = ⊤`
  have hf : (X ^ (m + 1) - X - 1 : ℚ[X]) = trinomial 0 1 (m + 1) (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  have hfm : (X ^ (m + 1) - X - 1 : ℚ[X]).Monic := by
    rw [hf]; exact trinomial_monic zero_lt_one (by omega)
  have hfd : (X ^ (m + 1) - X - 1 : ℚ[X]).natDegree = m + 1 := by
    rw [hf]; exact trinomial_natDegree zero_lt_one (by omega) one_ne_zero
  have haα : aeval α (X ^ (m + 1) - X - 1 : ℚ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_one]; rw [hα]; ring
  have hαint : IsIntegral ℚ α := ⟨_, hfm, by rw [← aeval_def]; exact haα⟩
  have hminα : minpoly ℚ α = X ^ (m + 1) - X - 1 :=
    (minpoly.eq_of_irreducible_of_monic (X_pow_sub_X_sub_one_irreducible_rat (by omega)) haα
      hfm).symm
  have hαtop : ℚ⟮α⟯ = ⊤ := by
    apply eq_of_le_of_finrank_eq le_top
    rw [adjoin.finrank hαint, hminα, hfd, finrank_top', hE]
  -- hence `ℚ⟮β⟯ = ⊤` and the minimal polynomial of `β` has degree `m + 1`
  have hβtop : ℚ⟮β⟯ = ⊤ := by
    rw [eq_top_iff, ← hαtop, adjoin_simple_le_iff]
    have hmem : -β⁻¹ ∈ ℚ⟮β⟯ := neg_mem (inv_mem (mem_adjoin_simple_self ℚ β))
    rwa [← hαβ] at hmem
  have hβint : IsIntegral ℚ β := .of_finite ℚ β
  have hβdeg : (minpoly ℚ β).natDegree = m + 1 := by
    rw [← adjoin.finrank hβint, hβtop, finrank_top', hE]
  -- `β` is a root of the monic degree-`(m + 1)` polynomial `x^(m+1) − x^m − (−1)^(m+1)`
  have hβrel : β ^ (m + 1) - β ^ m - (-1) ^ (m + 1) = 0 := by
    have e1 : α ^ (m + 1) * (-α⁻¹) ^ (m + 1) = (-1) ^ (m + 1) := by
      rw [← mul_pow, mul_neg, mul_inv_cancel₀ hα0]
    have e2 : α ^ (m + 1) * (-α⁻¹) ^ m = α * (-1) ^ m := by
      rw [pow_succ', mul_assoc, ← mul_pow, mul_neg, mul_inv_cancel₀ hα0]
    have key : α ^ (m + 1) * ((-α⁻¹) ^ (m + 1) - (-α⁻¹) ^ m - (-1) ^ (m + 1)) = 0 := by
      rw [mul_sub, mul_sub, e1, e2]
      linear_combination (-(-1) ^ (m + 1)) * hα
    rw [hβ]
    exact (mul_eq_zero.mp key).resolve_left (pow_ne_zero _ hα0)
  have hg : (X ^ (m + 1) - X ^ m - C ((-1) ^ (m + 1)) : ℚ[X])
      = trinomial 0 m (m + 1) (-(-1) ^ (m + 1)) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  have hgm : (X ^ (m + 1) - X ^ m - C ((-1) ^ (m + 1)) : ℚ[X]).Monic := by
    rw [hg]; exact trinomial_monic (by omega) (by omega)
  have hgd : (X ^ (m + 1) - X ^ m - C ((-1) ^ (m + 1)) : ℚ[X]).natDegree = m + 1 := by
    rw [hg]; exact trinomial_natDegree (by omega) (by omega) one_ne_zero
  have haβ : aeval β (X ^ (m + 1) - X ^ m - C ((-1) ^ (m + 1)) : ℚ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_neg, map_one]
    exact hβrel
  have hminβ : (X ^ (m + 1) - X ^ m - C ((-1) ^ (m + 1)) : ℚ[X]) = minpoly ℚ β :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hβint) hgm
      (minpoly.dvd ℚ β haβ) (by rw [hgd, hβdeg])
  have hgpos : 0 < (X ^ (m + 1) - X ^ m - C ((-1) ^ (m + 1)) : ℚ[X]).natDegree := by
    rw [hgd]; omega
  -- the trace is minus the next coefficient of the minimal polynomial
  have hfin : Module.finrank ℚ⟮β⟯ E = 1 := by
    rw [hβtop]; exact IntermediateField.finrank_top
  rw [_root_.trace_eq_finrank_mul_minpoly_nextCoeff ℚ β, hfin, ← hminβ,
    nextCoeff_of_natDegree_pos hgpos, hgd, Nat.add_sub_cancel, hg,
    trinomial_middle_coeff (by omega) (by omega)]
  simp

/-- Statement (12a), `n = 3`, re-derived from the general theorem (cross-check of
`trace_neg_inv_gen₃`). -/
theorem trace_neg_inv_gen₃' : Algebra.trace ℚ S₃ (-gen₃⁻¹) = 1 :=
  trace_neg_inv_of_pow_eq_add_one (by norm_num) finrank_S₃ gen₃_pow_three

/-- Statement (12a), `n = 4`, re-derived from the general theorem (cross-check of
`trace_neg_inv_gen₄`). -/
theorem trace_neg_inv_gen₄' : Algebra.trace ℚ S₄ (-gen₄⁻¹) = 1 :=
  trace_neg_inv_of_pow_eq_add_one (by norm_num) finrank_S₄ gen₄_pow_four

end HermiteCompositum.Instance
