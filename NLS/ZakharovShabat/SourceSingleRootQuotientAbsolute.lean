import NLS.ZakharovShabat.SourceSingleRootQuotientAnalytic
import NLS.SequenceSpaces.ShiftedHolderDecay

/-!
# Absolute convergence of the individual quotient factors

The free spectral terms cancel between numerator and denominator. The
remaining numerator displacement, midpoint displacement and square-root
correction form an ℓ¹ sequence. Normalized denominator factors tend to one,
so the quotient has absolutely summable individual deviations from one.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Individual quotient errors are absolutely summable, before any pairing. -/
theorem summable_norm_sourceSingleRootQuotient_error (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (a : Coeff p) (z : ℂ) :
    Summable (fun m : ℤ => ‖(displacedRoots a m-z)/sourceStandardRoot hp hp1 ψ m z-1‖) := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  let hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  let b : Coeff 1 := (Real.pi:ℂ)⁻¹ • Coeff.holderProduct (q := 1) a
    (Coeff.puncturedLattice p.conjExponent hq)
  have hb (m : ℤ) (hm : m ≠ 0) : b m = a m/((Real.pi:ℂ)*m) := by
    simp only [b,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      Coeff.holderProduct_apply,Coeff.puncturedLattice_apply,if_neg hm]
    field_simp
  let d : Coeff 1 := b-sourceStandardRootMidpointCorrection hp hp1 ψ-
    sourceStandardRootSqrtCorrectionCoeff hp hp1 ψ z
  have hd : Summable (fun m : ℤ => ‖d m‖) := by
    simpa only [ENNReal.toReal_one,Real.rpow_one] using
      (lp.memℓp d).summable (by norm_num : 0 < (1:ℝ≥0∞).toReal)
  let e := sourceStandardRootRelativeErrorCoeff hp hp1 ψ z
  have he : ∀ᶠ m : ℤ in cofinite, ‖e m‖ < (1/2:ℝ) :=
    (Coeff.tendsto_norm_apply_cofinite (by norm_num : (2:ℝ≥0∞) ≠ ⊤) e).eventually_lt_const (by norm_num)
  have hm0 : ∀ᶠ m : ℤ in cofinite, m ≠ 0 :=
    Filter.eventually_cofinite.mpr (by simp)
  apply Summable.of_norm_bounded_eventually (hd.mul_left 2)
  filter_upwards [he,hm0] with m he hm
  have heq : e m = sourceStandardRoot hp hp1 ψ m z/((Real.pi:ℂ)*m)-1 :=
    sourceStandardRootRelativeErrorCoeff_apply_of_ne hp hp1 ψ z m hm
  have hden : (1/2:ℝ) ≤ ‖1+e m‖ := by
    have hn := norm_sub_le (1+e m) (e m)
    have hc : (1+e m)-e m = 1 := by ring
    rw [hc,norm_one] at hn
    linarith
  have he0 : 1+e m ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hden)
  have hπ : (Real.pi:ℂ)*m ≠ 0 := mul_ne_zero
    (by exact_mod_cast Real.pi_ne_zero) (by exact_mod_cast hm)
  have hw : sourceStandardRoot hp hp1 ψ m z ≠ 0 := by
    intro hw
    apply he0
    rw [heq,hw]
    simp
  have hid : (displacedRoots a m-z)/sourceStandardRoot hp hp1 ψ m z-1 = d m/(1+e m) := by
    have hr := sourceStandardRootRelativeError_eq hp hp1 ψ m z hm
    change sourceStandardRoot hp hp1 ψ m z/((Real.pi:ℂ)*m)-1 = _ at hr
    have hdv : d m = a m/((Real.pi:ℂ)*m) -
        (sourceStandardRoot hp hp1 ψ m z/((Real.pi:ℂ)*m)-1) - z/((Real.pi:ℂ)*m) := by
      simp only [d,lp.coeFn_sub,Pi.sub_apply,hb m hm,sourceStandardRootMidpointCorrection_apply,
        if_neg hm,sourceStandardRootSqrtCorrectionCoeff_apply,sourceStandardRootSqrtCorrection,
        standardRootSqrtCorrection]
      rw [hr]
      ring
    rw [hdv,heq]
    unfold displacedRoots
    field_simp [hw,hπ]
    ring
  rw [norm_norm,hid,norm_div]
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) hden)).mpr
  nlinarith [norm_nonneg (d m)]

/-- Replace the omitted factor by one to index the product over all integers. -/
def sourceSingleRootQuotientFactor (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (a : Coeff p) (z : ℂ) (n m : ℤ) : ℂ :=
  if m = n then 1 else (displacedRoots a m-z)/sourceStandardRoot hp hp1 ψ m z

/-- Omitting any one factor preserves absolute convergence. -/
theorem summable_norm_sourceSingleRootQuotientFactor_sub_one (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (a : Coeff p) (z : ℂ) (n : ℤ) :
    Summable (fun m : ℤ => ‖sourceSingleRootQuotientFactor hp hp1 ψ a z n m-1‖) := by
  apply (summable_norm_sourceSingleRootQuotient_error hp hp1 ψ a z).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro m
  by_cases hm : m = n
  · simp [sourceSingleRootQuotientFactor,hm]
  · simp [sourceSingleRootQuotientFactor,hm]

/-- The quotient factors have an unconditional product, even when numerator roots collide. -/
theorem multipliable_sourceSingleRootQuotientFactor (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (a : Coeff p) (z : ℂ) (n : ℤ) :
    Multipliable (sourceSingleRootQuotientFactor hp hp1 ψ a z n) := by
  convert multipliable_one_add_of_summable
    (summable_norm_sourceSingleRootQuotientFactor_sub_one hp hp1 ψ a z n) using 1
  ext m
  ring

/-- Every finite factor product is the literal product with the selected index erased. -/
theorem prod_sourceSingleRootQuotientFactor (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (a : Coeff p) (z : ℂ) (n : ℤ) (s : Finset ℤ) :
    (∏ m ∈ s, sourceSingleRootQuotientFactor hp hp1 ψ a z n m) =
      ∏ m ∈ s.erase n, (displacedRoots a m-z)/sourceStandardRoot hp hp1 ψ m z := by
  unfold sourceSingleRootQuotientFactor
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one,one_mul]
  congr 1
  ext m
  simp only [Finset.mem_filter,Finset.mem_erase]
  tauto

/-- On the natural domain, the unordered product is exactly the analytic quotient. -/
theorem hasProd_sourceSingleRootQuotientFactor (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (a : Coeff p) (z : ℂ) (n : ℤ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    HasProd (sourceSingleRootQuotientFactor hp hp1 ψ a z n)
      (sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ))) := by
  have hprod := (multipliable_sourceSingleRootQuotientFactor hp hp1 ψ a z n).hasProd
  have hseq := hprod.comp Finset.tendsto_Icc_neg
  simp only [Function.comp_def,prod_sourceSingleRootQuotientFactor] at hseq
  have hknown := tendsto_sourceSingleRootQuotientPartialProduct hp hp1 n univ (z,(a,ψ)) ⟨mem_univ _,hz⟩
  have he := tendsto_nhds_unique hseq hknown
  exact he ▸ hprod

/-- The product can equivalently be indexed by the integers different from n. -/
theorem hasProd_sourceSingleRootQuotient_subtype (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (a : Coeff p) (z : ℂ) (n : ℤ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    HasProd (fun m : {m : ℤ // m ≠ n} =>
      (displacedRoots a m-z)/sourceStandardRoot hp hp1 ψ m z)
      (sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ))) := by
  apply (hasProd_subtype_iff_mulIndicator (s := {m : ℤ | m ≠ n})
    (f := fun m => (displacedRoots a m-z)/sourceStandardRoot hp hp1 ψ m z)).mpr
  convert hasProd_sourceSingleRootQuotientFactor hp hp1 ψ a z n hz using 1
  ext m
  by_cases hm : m = n <;> simp [Set.mulIndicator,sourceSingleRootQuotientFactor,hm]

/-- The net of all finite products with the selected index erased converges to the quotient. -/
theorem tendsto_finset_sourceSingleRootQuotient (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (a : Coeff p) (z : ℂ) (n : ℤ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    Tendsto (fun s : Finset ℤ => ∏ m ∈ s.erase n,
      (displacedRoots a m-z)/sourceStandardRoot hp hp1 ψ m z) atTop
      (𝓝 (sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ)))) := by
  simpa only [HasProd,SummationFilter.unconditional,prod_sourceSingleRootQuotientFactor] using
    hasProd_sourceSingleRootQuotientFactor hp hp1 ψ a z n hz

end NLS.ZakharovShabat
