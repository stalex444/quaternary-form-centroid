module
public import Mathlib

@[expose] public section
/-!
# Shared definitions

The definitions on which the eighteen compared statements rest, with the supporting theorems
their bodies use (irreducibility of `x³ − x − 1` and `x⁴ − x − 1`, integrality of the
generators, and so on). The block between the `BEGIN`/`END SHARED DEFINITIONS` markers is copied
byte for byte into `Challenge.lean`, so the Challenge imports Mathlib only and elaborates the
same declarations, under the same names, as the proof modules, which are all built on this file.
-/

-- BEGIN SHARED DEFINITIONS
-- The definitions of this entry that the compared statements use, with the theorems their
-- bodies depend on (for instance the irreducibility of x³ − x − 1 and x⁴ − x − 1, which makes `L`
-- a field). This block is, byte for byte, the body of `HermiteCompositum/Defs.lean`, on which the
-- proof modules are built; both files import Mathlib only.

-- The Hermite form and the root sets of statement 1.
namespace HermiteCompositum

open Polynomial Finset
open scoped ComplexConjugate

noncomputable section

/-- The complex roots of a real polynomial, as a multiset (with multiplicity). -/
def croots (f : ℝ[X]) : Multiset ℂ := (f.map (algebraMap ℝ ℂ)).roots

/-- The `k`-th power sum `s_k = Re ∑_α α^k` of the complex roots, counted with multiplicity
(the sum is real: `ofReal_powerSum` in `HermiteCompositum/Hermite.lean`). -/
def powerSum (f : ℝ[X]) (k : ℕ) : ℝ := ((croots f).map (· ^ k)).sum.re

/-- The Hermite (power-sum Hankel) matrix `(s_{i+j})_{i,j<n}`. -/
def hermiteMatrix (f : ℝ[X]) : Matrix (Fin f.natDegree) (Fin f.natDegree) ℝ :=
  Matrix.of fun i j => powerSum f ((i : ℕ) + (j : ℕ))

/-- The Hermite form `c ↦ ∑_{i,j<n} s_{i+j} c_i c_j` as a quadratic form on `Fin n → ℝ`. -/
def hermiteForm (f : ℝ[X]) : QuadraticForm ℝ (Fin f.natDegree → ℝ) :=
  (hermiteMatrix f).toQuadraticForm'

/-- `D`: the set of distinct complex roots. -/
def distinctRoots (f : ℝ[X]) : Finset ℂ := (croots f).toFinset

/-- `R = D ∩ ℝ`: the distinct real roots (as complex numbers with zero imaginary part). -/
def realRoots (f : ℝ[X]) : Finset ℂ := (distinctRoots f).filter (fun z => z.im = 0)

/-- `C⁺`: the distinct roots in the open upper half plane. -/
def upperRoots (f : ℝ[X]) : Finset ℂ := (distinctRoots f).filter (fun z => 0 < z.im)

end

end HermiteCompositum

-- The trace projection and the transverse form of statement 5.
namespace HermiteCompositum

open Module QuadraticForm QuadraticMap

section Tower

variable {K E : Type*} [Field K] [Field E] [Algebra K E] (F : IntermediateField K E)
  [FiniteDimensional K E]

/-- The trace projection `π = [E:F]⁻¹ · Tr_{E/F}`, as an `F`-linear endomorphism of `E`
with values in (the image of) `F`. -/
noncomputable def traceProj : E →ₗ[F] E :=
  ((finrank F E : F)⁻¹) • ((Algebra.linearMap F E).comp (Algebra.trace F E))

end Tower

section NumberField

open NumberField NumberField.InfinitePlace

variable {E : Type*} [Field E] [NumberField E] (F : IntermediateField ℚ E)

/-- The **transverse form**: `Tr_{E/ℚ}(x²)` restricted to `ker Tr_{E/F} = F^⊥`. -/
noncomputable abbrev transverseForm : QuadraticForm ℚ
    (LinearMap.ker ((Algebra.trace F E).restrictScalars ℚ)) :=
  (Algebra.traceForm ℚ E).toQuadraticMap.restrict
    (LinearMap.ker ((Algebra.trace F E).restrictScalars ℚ))

end NumberField

end HermiteCompositum

-- The two polynomials and their irreducibility over `ℚ`, ported from the registered entry
-- PALOMAR-2026-09-02-000014, every statement unchanged. Three proofs differ from that entry: in
-- `cubic_irred_zmod2`, `monic_deg2_no_root_eq` and `quartic_irred_zmod2` an `omega` step is
-- replaced by an explicit term (`omega` emits auxiliary lemmas whose names contain the module
-- name, which differs between `Challenge.lean` and `HermiteCompositum/Defs.lean`), and
-- `quartic_irred_zmod2` also carries the one-line `ZMod 2` fix made when the port was first
-- compiled at this pin.
namespace HermiteCompositum.Port014

open Polynomial Module

/-- The quartic `X⁴ − X − 1`. -/
noncomputable def fQ : ℚ[X] := X ^ 4 - X - 1

/-- The cubic `X³ − X − 1`. -/
noncomputable def fρ : ℚ[X] := X ^ 3 - X - 1

theorem fQ_monic : fQ.Monic := by
  unfold fQ; monicity!

theorem fρ_monic : fρ.Monic := by
  unfold fρ; monicity!

theorem fQ_natDegree : fQ.natDegree = 4 := by
  unfold fQ; compute_degree!

theorem fρ_natDegree : fρ.natDegree = 3 := by
  unfold fρ; compute_degree!

/-- The cubic x³ - x - 1 over ℤ. -/
noncomputable def cubicZ : ℤ[X] := X ^ 3 - X - 1

/-- The quartic x⁴ - x - 1 over ℤ. -/
noncomputable def quarticZ : ℤ[X] := X ^ 4 - X - 1

lemma cubicZ_monic : (cubicZ).Monic := by
  unfold cubicZ
  monicity!

lemma quarticZ_monic : (quarticZ).Monic := by
  unfold quarticZ
  monicity!

/-- The image of cubicZ under ℤ → ZMod 2. -/
lemma cubicZ_map2 : cubicZ.map (Int.castRingHom (ZMod 2)) = X ^ 3 + X + 1 := by
  unfold cubicZ
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  have h2 : (2 : (ZMod 2)[X]) = 0 := by
    have e : (2 : ZMod 2) = 0 := by decide
    calc (2 : (ZMod 2)[X]) = C (2 : ZMod 2) := (C_ofNat 2).symm
      _ = C (0 : ZMod 2) := by rw [e]
      _ = 0 := by simp
  linear_combination (-(X : (ZMod 2)[X]) - 1) * h2

/-- x³ + x + 1 is irreducible over 𝔽₂ (it has no root in 𝔽₂). -/
lemma cubic_irred_zmod2 : Irreducible (X ^ 3 + X + 1 : (ZMod 2)[X]) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · -- natDegree ∈ [1,3]
    have hd : (X ^ 3 + X + 1 : (ZMod 2)[X]).natDegree = 3 := by compute_degree!
    rw [Finset.mem_Icc, hd]
    exact ⟨by norm_num, le_rfl⟩
  · -- no root
    intro x
    rw [IsRoot.def]
    simp only [eval_add, eval_pow, eval_X, eval_one]
    fin_cases x <;> decide

/-- x³ - x - 1 is irreducible over ℤ. -/
lemma cubicZ_irred : Irreducible cubicZ := by
  apply cubicZ_monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 2))
  rw [cubicZ_map2]
  exact cubic_irred_zmod2

/-- x³ - x - 1 is irreducible over ℚ. -/
theorem cubicQ_irreducible :
    Irreducible (X ^ 3 - X - 1 : ℚ[X]) := by
  have h := (cubicZ_monic.irreducible_iff_irreducible_map_fraction_map
    (K := ℚ)).mp cubicZ_irred
  have hmap : cubicZ.map (algebraMap ℤ ℚ) = (X ^ 3 - X - 1 : ℚ[X]) := by
    unfold cubicZ
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  rwa [hmap] at h

/-! ### The quartic x⁴ - x - 1 -/

/-- The image of quarticZ under ℤ → ZMod 2 is x⁴ + x + 1. -/
lemma quarticZ_map2 : quarticZ.map (Int.castRingHom (ZMod 2)) = X ^ 4 + X + 1 := by
  unfold quarticZ
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  have h2 : (2 : (ZMod 2)[X]) = 0 := by
    have e : (2 : ZMod 2) = 0 := by decide
    calc (2 : (ZMod 2)[X]) = C (2 : ZMod 2) := (C_ofNat 2).symm
      _ = C (0 : ZMod 2) := by rw [e]
      _ = 0 := by simp
  linear_combination (-(X : (ZMod 2)[X]) - 1) * h2

/-- x⁴ + x + 1 has no root in 𝔽₂. -/
lemma quartic_no_root_zmod2 (x : ZMod 2) : ¬ (X ^ 4 + X + 1 : (ZMod 2)[X]).IsRoot x := by
  rw [IsRoot.def]
  simp only [eval_add, eval_pow, eval_X, eval_one]
  fin_cases x <;> decide

/-- A monic degree-2 polynomial over 𝔽₂ with no root equals X²+X+1. -/
lemma monic_deg2_no_root_eq (q : (ZMod 2)[X]) (hm : q.Monic) (hnd : q.natDegree = 2)
    (hr : ∀ x, ¬ q.IsRoot x) : q = X ^ 2 + X + 1 := by
  have hform : q = C (q.coeff 0) + C (q.coeff 1) * X + C (q.coeff 2) * X ^ 2 := by
    have h3 : q.natDegree < 3 := lt_of_eq_of_lt hnd (by norm_num)
    have h := q.as_sum_range_C_mul_X_pow' h3
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at h
    conv_lhs => rw [h]
    ring
  have hc2 : q.coeff 2 = 1 := by
    have := hm.coeff_natDegree
    rwa [hnd] at this
  -- evaluate roots at 0 and 1
  have h0 := hr 0
  have h1 := hr 1
  rw [IsRoot.def, hform] at h0 h1
  simp only [eval_add, eval_mul, eval_C, eval_X, hc2,
    mul_zero, mul_one, pow_two, add_zero] at h0 h1
  -- h0: ¬ (q.coeff 0 = 0); h1: ¬ (q.coeff 0 + q.coeff 1 + 1 = 0)
  have hcoeff0 : q.coeff 0 = 1 := by
    revert h0; generalize q.coeff 0 = a; clear hform; revert a; decide
  have hcoeff1 : q.coeff 1 = 1 := by
    rw [hcoeff0] at h1
    revert h1; generalize q.coeff 1 = b; clear hform; revert b; decide
  rw [hform, hc2, hcoeff0, hcoeff1, C_1]
  ring

/-- x⁴ + x + 1 is irreducible over 𝔽₂. -/
lemma quartic_irred_zmod2 : Irreducible (X ^ 4 + X + 1 : (ZMod 2)[X]) := by
  set p : (ZMod 2)[X] := X ^ 4 + X + 1 with hp
  have hm : p.Monic := by rw [hp]; monicity!
  have hnd : p.natDegree = 4 := by rw [hp]; compute_degree!
  have hp1 : p ≠ 1 := by
    intro h; rw [h, natDegree_one] at hnd; exact absurd hnd (by norm_num)
  rw [hm.irreducible_iff_lt_natDegree_lt hp1]
  -- natDegree p / 2 = 2
  rw [hnd]
  intro q hqm hq hdvd
  rw [Finset.mem_Ioc] at hq
  obtain ⟨hq0, hq2⟩ := hq
  -- Case on natDegree q (1 or 2)
  interval_cases hqd : q.natDegree
  · -- natDegree q = 1
    have heq : q = X + C (q.coeff 0) := hqm.eq_X_add_C hqd
    obtain ⟨r, hr⟩ := hdvd
    set a := q.coeff 0 with ha
    -- p has root -a
    have : p.IsRoot (-a) := by
      rw [IsRoot.def, hr, eval_mul, heq]
      simp only [eval_add, eval_X, eval_C]; exact mul_eq_zero_of_left (by generalize a = b; fin_cases b <;> rfl) _
    rw [hp] at this
    exact quartic_no_root_zmod2 _ this
  · -- natDegree q = 2
    obtain ⟨r, hr⟩ := hdvd
    have hrm : r.Monic := hqm.of_mul_monic_left (hr ▸ hm)
    have hrnd : r.natDegree = 2 := by
      have hdeg : q.natDegree + r.natDegree = 4 := by
        rw [← hqm.natDegree_mul hrm, ← hr, hnd]
      rw [hqd] at hdeg
      exact Nat.add_left_cancel (hdeg.trans (by norm_num : (4 : ℕ) = 2 + 2))
    -- q has no root (else linear factor of p gives root of p)
    have hqnoroot : ∀ x, ¬ q.IsRoot x := by
      intro x hx
      have : p.IsRoot x := by
        rw [hr, IsRoot.def, eval_mul]
        rw [IsRoot.def] at hx; rw [hx, zero_mul]
      rw [hp] at this; exact quartic_no_root_zmod2 _ this
    have hrnoroot : ∀ x, ¬ r.IsRoot x := by
      intro x hx
      have : p.IsRoot x := by
        rw [hr, IsRoot.def, eval_mul]
        rw [IsRoot.def] at hx; rw [hx, mul_zero]
      rw [hp] at this; exact quartic_no_root_zmod2 _ this
    -- so q = r = X²+X+1, p = (X²+X+1)², contradiction
    have hqeq : q = X ^ 2 + X + 1 := monic_deg2_no_root_eq q hqm hqd hqnoroot
    have hreq : r = X ^ 2 + X + 1 := monic_deg2_no_root_eq r hrm hrnd hrnoroot
    rw [hqeq, hreq, hp] at hr
    -- product over 𝔽₂: (X²+X+1)² = X⁴+X²+1
    have hprod : (X ^ 2 + X + 1 : (ZMod 2)[X]) * (X ^ 2 + X + 1) = X ^ 4 + X ^ 2 + 1 := by
      have h2 : (2 : (ZMod 2)[X]) = 0 := by
        have e : (2 : ZMod 2) = 0 := by decide
        calc (2 : (ZMod 2)[X]) = C (2 : ZMod 2) := (C_ofNat 2).symm
          _ = C (0 : ZMod 2) := by rw [e]
          _ = 0 := by simp
      linear_combination (X ^ 3 + X ^ 2 + X) * h2
    rw [hprod] at hr
    -- compare coeff 1: LHS = 1, RHS = 0
    have hc := congrArg (fun t => Polynomial.coeff t 1) hr
    simp only [coeff_add, coeff_X_pow, coeff_X, coeff_one] at hc
    exact absurd hc (by decide)

/-- x⁴ - x - 1 is irreducible over ℤ. -/
lemma quarticZ_irred : Irreducible quarticZ := by
  apply quarticZ_monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 2))
  rw [quarticZ_map2]
  exact quartic_irred_zmod2

/-- x⁴ - x - 1 is irreducible over ℚ. -/
theorem quarticQ_irreducible :
    Irreducible (X ^ 4 - X - 1 : ℚ[X]) := by
  have h := (quarticZ_monic.irreducible_iff_irreducible_map_fraction_map
    (K := ℚ)).mp quarticZ_irred
  have hmap : quarticZ.map (algebraMap ℤ ℚ) = (X ^ 4 - X - 1 : ℚ[X]) := by
    unfold quarticZ
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  rwa [hmap] at h

end HermiteCompositum.Port014

-- The degree-12 tower `ℚ ⊂ K₃ ⊂ L`, its generators, the sectors `S₃`, `S₄` and the integral maps
-- of statement 12.
namespace HermiteCompositum.Instance

open Polynomial NumberField NumberField.InfinitePlace IntermediateField Module

/-- An irreducible monic polynomial over a field `k` stays irreducible over a finite extension
`F/k` whose degree is coprime to the degree of the polynomial. (Used for `Y⁴ − Y − 1` over the
cubic field; the general statement costs nothing extra.) -/
theorem irreducible_map_of_coprime_finrank {k F : Type*} [Field k] [Field F] [Algebra k F]
    [FiniteDimensional k F] {p : k[X]} (hp : Irreducible p) (hm : p.Monic)
    (hcop : Nat.Coprime p.natDegree (Module.finrank k F)) :
    Irreducible (p.map (algebraMap k F)) := by
  classical
  have hp0 : p ≠ 0 := hm.ne_zero
  have hdeg : (p.map (algebraMap k (AlgebraicClosure F))).degree ≠ 0 := by
    rw [degree_map]; exact (degree_pos_of_irreducible hp).ne'
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_root _ hdeg
  have hβ' : aeval β p = 0 := by rwa [aeval_def, ← eval_map]
  have hint : IsIntegral k β := ⟨p, hm, by rwa [← aeval_def]⟩
  have hmin : minpoly k β = p := (minpoly.eq_of_irreducible_of_monic hp hβ' hm).symm
  have hintF : IsIntegral F β := hint.tower_top
  have hqdvd : minpoly F β ∣ p.map (algebraMap k F) := by
    have := minpoly.dvd_map_of_isScalarTower k F β
    rwa [hmin] at this
  have hpF0 : p.map (algebraMap k F) ≠ 0 := Polynomial.map_ne_zero hp0
  have hqm : (minpoly F β).Monic := minpoly.monic hintF
  have hqle : (minpoly F β).natDegree ≤ p.natDegree := by
    have := hqm.natDegree_le_of_dvd hpF0 hqdvd
    rwa [natDegree_map] at this
  have h2 : finrank k F⟮β⟯ = finrank k F * (minpoly F β).natDegree := by
    rw [← adjoin.finrank hintF, Module.finrank_mul_finrank k F F⟮β⟯]
  -- inside `F⟮β⟯`, the generator spans a degree-`n` subfield over `k`, so `n ∣ m · d`
  have hβ'p : aeval (AdjoinSimple.gen F β) p = 0 := by
    rw [← Polynomial.aeval_map_algebraMap F]
    exact Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hqdvd (aeval_gen_minpoly F β)
  have hβ'int : IsIntegral k (AdjoinSimple.gen F β) := ⟨p, hm, by rwa [← aeval_def]⟩
  have hmin' : minpoly k (AdjoinSimple.gen F β) = p :=
    (minpoly.eq_of_irreducible_of_monic hp hβ'p hm).symm
  have h3 : finrank k k⟮AdjoinSimple.gen F β⟯ ∣ finrank k F⟮β⟯ := by
    have := finrank_dvd_of_le_right (le_top : k⟮AdjoinSimple.gen F β⟯ ≤ ⊤)
    rwa [finrank_top'] at this
  rw [adjoin.finrank hβ'int, hmin', h2] at h3
  have h5 : p.natDegree ∣ (minpoly F β).natDegree := hcop.dvd_of_dvd_mul_left h3
  have hqpos : 0 < (minpoly F β).natDegree := minpoly.natDegree_pos hintF
  have hqeq : (minpoly F β).natDegree = p.natDegree :=
    le_antisymm hqle (Nat.le_of_dvd hqpos h5)
  have hmF : (p.map (algebraMap k F)).Monic := hm.map _
  have hd : (p.map (algebraMap k F)).natDegree ≤ (minpoly F β).natDegree := by
    rw [natDegree_map, hqeq]
  rw [Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm hmF hqdvd hd]
  exact minpoly.irreducible hintF

/-- Two `ℚ`-algebra structures on a semiring coincide (the bridge between
`DivisionRing.toRatAlgebra` and `AdjoinRoot.instAlgebra`). -/
theorem algebraRat_eq {A : Type*} [Semiring A] (P Q : Algebra ℚ A) : P = Q :=
  Algebra.algebra_ext P Q fun r =>
    congrArg (fun f : ℚ →+* A => f r)
      (RingHom.ext_rat (@algebraMap ℚ A _ _ P) (@algebraMap ℚ A _ _ Q))

open Port014 in
/-- `X³ − X − 1` is irreducible over `ℚ` (from the port of 000014). -/
instance : Fact (Irreducible fρ) := ⟨cubicQ_irreducible⟩

/-- The cubic field `K₃ = ℚ[X]/(X³ − X − 1)` (the base of the tower). -/
abbrev K₃ := AdjoinRoot Port014.fρ

theorem finrank_K₃ : Module.finrank ℚ K₃ = 3 := by
  have h := (AdjoinRoot.powerBasis' Port014.fρ_monic).finrank
  rw [AdjoinRoot.powerBasis'_dim, Port014.fρ_natDegree] at h
  convert h

/-- The quartic `Y⁴ − Y − 1` read over the cubic field. -/
noncomputable def g : K₃[X] := Port014.fQ.map (algebraMap ℚ K₃)

theorem g_monic : g.Monic := Port014.fQ_monic.map _

/-- **Irreducibility over the cubic field**: `Y⁴ − Y − 1` stays irreducible over the cubic field (degrees `3` and
`4` are coprime). -/
theorem g_irreducible : Irreducible g :=
  irreducible_map_of_coprime_finrank Port014.quarticQ_irreducible Port014.fQ_monic
    (by rw [Port014.fQ_natDegree, finrank_K₃]; decide)

instance : Fact (Irreducible g) := ⟨g_irreducible⟩

/-- The degree-12 field `L = K₃[Y]/(Y⁴ − Y − 1)`. -/
abbrev L := AdjoinRoot g

instance : Module.Finite K₃ L := g_monic.finite_adjoinRoot

instance : NumberField L := NumberField.of_module_finite K₃ L

/-- `ρ ∈ L`: the image of the cubic root. -/
noncomputable abbrev ρ : L := algebraMap K₃ L (AdjoinRoot.root Port014.fρ)

/-- `Q ∈ L`: the quartic root. -/
noncomputable abbrev Q : L := AdjoinRoot.root g

theorem aeval_ρ : aeval ρ Port014.fρ = 0 := by
  have h := AdjoinRoot.aeval_eq (f := Port014.fρ) Port014.fρ
  rw [AdjoinRoot.mk_self] at h
  have h2 := congrArg (algebraMap K₃ L) h
  rw [map_zero] at h2
  rw [Polynomial.aeval_algebraMap_apply]
  convert h2 <;> exact algebraRat_eq _ _

theorem aeval_Q : aeval Q Port014.fQ = 0 := by
  rw [← Polynomial.aeval_map_algebraMap K₃, ← g, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

theorem minpoly_ρ : minpoly ℚ ρ = Port014.fρ :=
  (minpoly.eq_of_irreducible_of_monic Port014.cubicQ_irreducible aeval_ρ Port014.fρ_monic).symm

theorem minpoly_Q : minpoly ℚ Q = Port014.fQ :=
  (minpoly.eq_of_irreducible_of_monic Port014.quarticQ_irreducible aeval_Q Port014.fQ_monic).symm

/-- The cubic sector `S₃ = ℚ⟮ρ⟯`. -/
noncomputable def S₃ : IntermediateField ℚ L := ℚ⟮ρ⟯

/-- The quartic sector `S₄ = ℚ⟮Q⟯`. -/
noncomputable def S₄ : IntermediateField ℚ L := ℚ⟮Q⟯

/-- The generator `ρ` seen inside `S₃`. -/
noncomputable def gen₃ : S₃ := AdjoinSimple.gen ℚ ρ

/-- The generator `Q` seen inside `S₄`. -/
noncomputable def gen₄ : S₄ := AdjoinSimple.gen ℚ Q

theorem algebraMap_gen₃ : algebraMap S₃ L gen₃ = ρ := AdjoinSimple.algebraMap_gen ℚ ρ

theorem algebraMap_gen₄ : algebraMap S₄ L gen₄ = Q := AdjoinSimple.algebraMap_gen ℚ Q

theorem minpoly_gen₃ : minpoly ℚ gen₃ = Port014.fρ := (minpoly_gen ℚ ρ).trans minpoly_ρ

theorem minpoly_gen₄ : minpoly ℚ gen₄ = Port014.fQ := (minpoly_gen ℚ Q).trans minpoly_Q

theorem aeval_gen₃ : aeval gen₃ Port014.fρ = 0 := by
  have h := minpoly.aeval ℚ gen₃; rwa [minpoly_gen₃] at h

theorem aeval_gen₄ : aeval gen₄ Port014.fQ = 0 := by
  have h := minpoly.aeval ℚ gen₄; rwa [minpoly_gen₄] at h

theorem gen₃_isIntegral_int : IsIntegral ℤ gen₃ := by
  refine ⟨Port014.cubicZ, Port014.cubicZ_monic, ?_⟩
  have hmap : Port014.cubicZ.map (algebraMap ℤ ℚ) = Port014.fρ := by
    simp [Port014.cubicZ, Port014.fρ, Polynomial.map_sub, Polynomial.map_pow]
  rw [← aeval_def, ← Polynomial.aeval_map_algebraMap ℚ, hmap]
  exact aeval_gen₃

theorem gen₄_isIntegral_int : IsIntegral ℤ gen₄ := by
  refine ⟨Port014.quarticZ, Port014.quarticZ_monic, ?_⟩
  have hmap : Port014.quarticZ.map (algebraMap ℤ ℚ) = Port014.fQ := by
    simp [Port014.quarticZ, Port014.fQ, Polynomial.map_sub, Polynomial.map_pow]
  rw [← aeval_def, ← Polynomial.aeval_map_algebraMap ℚ, hmap]
  exact aeval_gen₄

/-- `ρ` as an element of `𝓞 S₃`. -/
noncomputable def θ₃ : 𝓞 S₃ := ⟨gen₃, gen₃_isIntegral_int⟩

/-- `Q` as an element of `𝓞 S₄`. -/
noncomputable def θ₄ : 𝓞 S₄ := ⟨gen₄, gen₄_isIntegral_int⟩

theorem ρ_isIntegral_int : IsIntegral ℤ ρ := by
  rw [← algebraMap_gen₃]; exact gen₃_isIntegral_int.map (IsScalarTower.toAlgHom ℤ S₃ L)

theorem Q_isIntegral_int : IsIntegral ℤ Q := by
  rw [← algebraMap_gen₄]; exact gen₄_isIntegral_int.map (IsScalarTower.toAlgHom ℤ S₄ L)

/-- `ρ` as an element of `𝓞 L`. -/
noncomputable def ρ' : 𝓞 L := ⟨ρ, ρ_isIntegral_int⟩

/-- `Q` as an element of `𝓞 L`. -/
noncomputable def Q' : 𝓞 L := ⟨Q, Q_isIntegral_int⟩

/-- The relative trace carries `𝓞 L` into `𝓞 S₃`. -/
theorem trace_S₃_isIntegral (x : 𝓞 L) :
    IsIntegral ℤ (Algebra.trace S₃ L (algebraMap (𝓞 L) L x)) :=
  Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe x)

/-- The relative trace carries `𝓞 L` into `𝓞 S₄`. -/
theorem trace_S₄_isIntegral (x : 𝓞 L) :
    IsIntegral ℤ (Algebra.trace S₄ L (algebraMap (𝓞 L) L x)) :=
  Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe x)

/-- `Tr_{L/S₃}` restricted to the rings of integers, as a `ℤ`-linear map `𝓞 L → 𝓞 S₃`. -/
noncomputable def T₃ : 𝓞 L →ₗ[ℤ] 𝓞 S₃ where
  toFun x := ⟨Algebra.trace S₃ L (algebraMap (𝓞 L) L x), trace_S₃_isIntegral x⟩
  map_add' x y := by
    apply RingOfIntegers.ext
    show Algebra.trace S₃ L (algebraMap (𝓞 L) L (x + y))
      = Algebra.trace S₃ L (algebraMap (𝓞 L) L x) + Algebra.trace S₃ L (algebraMap (𝓞 L) L y)
    rw [map_add, map_add]
  map_smul' n x := by
    apply RingOfIntegers.ext
    show Algebra.trace S₃ L (algebraMap (𝓞 L) L (n • x))
      = n • Algebra.trace S₃ L (algebraMap (𝓞 L) L x)
    rw [map_zsmul, map_zsmul]

/-- `Tr_{L/S₄}` restricted to the rings of integers, as a `ℤ`-linear map `𝓞 L → 𝓞 S₄`. -/
noncomputable def T₄ : 𝓞 L →ₗ[ℤ] 𝓞 S₄ where
  toFun x := ⟨Algebra.trace S₄ L (algebraMap (𝓞 L) L x), trace_S₄_isIntegral x⟩
  map_add' x y := by
    apply RingOfIntegers.ext
    show Algebra.trace S₄ L (algebraMap (𝓞 L) L (x + y))
      = Algebra.trace S₄ L (algebraMap (𝓞 L) L x) + Algebra.trace S₄ L (algebraMap (𝓞 L) L y)
    rw [map_add, map_add]
  map_smul' n x := by
    apply RingOfIntegers.ext
    show Algebra.trace S₄ L (algebraMap (𝓞 L) L (n • x))
      = n • Algebra.trace S₄ L (algebraMap (𝓞 L) L x)
    rw [map_zsmul, map_zsmul]

/-- The section `b ↦ −Q⁻¹·b = (1 − Q³)·b` of `T₃`, as a `ℤ`-linear map `𝓞 S₃ → 𝓞 L`. -/
noncomputable def σ₃ : 𝓞 S₃ →ₗ[ℤ] 𝓞 L :=
  (LinearMap.mulLeft ℤ (1 - Q' ^ 3)).comp (algebraMap (𝓞 S₃) (𝓞 L)).toIntAlgHom.toLinearMap

/-- The section `b ↦ −ρ⁻¹·b = (1 − ρ²)·b` of `T₄`, as a `ℤ`-linear map `𝓞 S₄ → 𝓞 L`. -/
noncomputable def σ₄ : 𝓞 S₄ →ₗ[ℤ] 𝓞 L :=
  (LinearMap.mulLeft ℤ (1 - ρ' ^ 2)).comp (algebraMap (𝓞 S₄) (𝓞 L)).toIntAlgHom.toLinearMap

end HermiteCompositum.Instance

-- The ruler polynomial of statement 15 and root-rigidity (statement 17).
namespace HermiteCompositum

open Polynomial Module Matrix

/-- `rulerPoly` = `X ^ 12 - 3 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 6 - X ^ 5 - 3 * X ^ 4 - X ^ 3 + X - 1` over `ℤ`. -/
noncomputable def rulerPoly : ℤ[X] := X ^ 12 - 3 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 6 - X ^ 5 - 3 * X ^ 4 - X ^ 3 + X - 1

/-- The ruler polynomial over `ℚ` (the form in which `minpoly ℚ (ρQ)` is stated). -/
noncomputable def rulerPolyQ : ℚ[X] :=
  X ^ 12 - 3 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 6 - X ^ 5 - 3 * X ^ 4 - X ^ 3 + X - 1

/-- **Root-rigidity**: no irreducible polynomial over `ℚ` has two distinct roots in `L`
(in particular, every subfield of `L` has trivial automorphism group over `ℚ`). -/
def RootRigid (L : Type*) [Field L] [Algebra ℚ L] : Prop :=
  ∀ α β : L, minpoly ℚ α = minpoly ℚ β → α = β

end HermiteCompositum
-- END SHARED DEFINITIONS
