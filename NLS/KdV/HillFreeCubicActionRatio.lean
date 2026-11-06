import NLS.KdV.HillFreeCubicMomentFactor

/-! # The actual free-normalized cubic moment divided by squared raw action -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The physical cubic period is the square of the RAW Arnold action
times a rough-source analytic factor with exact free value -3/(8*pi*n).
The multiplicative identity includes collapsed gaps; it never divides
by an action or assumes that an open gap stays open. -/
theorem exists_hillFree_analytic_cubic_action_ratio (n : ℕ+) :
    ∃ K : PeriodOneHminusOne → ℂ, AnalyticAt ℂ K 0 ∧ K 0=-3/(8*(n : ℂ)*Real.pi) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
        hillHminusRealGapCubicContourMoment (hillOriginalHminusSource p.val)
          (hillOriginalHminusSource_real p.val p.property.2) n =
          (hillRealGapIntegral p.val p.property.1 p.property.2 (n : ℕ) 0 : ℂ)^2*
            K (hillOriginalHminusSource p.val) := by
  obtain ⟨C,hC,hC0,hphys⟩ := exists_hillFree_analytic_cubic_gap_factor h0q h0r n
  let A := hillHminusLocalActionGapRatio h0q h0r n
  let K : PeriodOneHminusOne → ℂ := fun q => C q/(A q)^2
  have hA : AnalyticAt ℂ A 0 := analyticAt_hillHminusLocalActionGapRatio_zero h0q h0r n
  have hA0 : A 0≠0 := by
    change hillHminusLocalActionGapRatio h0q h0r n 0 ≠ 0
    rw [hillHminusLocalActionGapRatio_zero]
    apply inv_ne_zero
    have hn : (n : ℂ) ≠ 0 := by exact_mod_cast n.pos.ne'
    exact mul_ne_zero (mul_ne_zero (by norm_num) hn) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hK : AnalyticAt ℂ K 0 := hC.div (hA.pow 2) (pow_ne_zero 2 hA0)
  have hK0 : K 0=-3/(8*(n : ℂ)*Real.pi) := by
    change C 0/(hillHminusLocalActionGapRatio h0q h0r n 0)^2=_
    rw [hC0,hillHminusLocalActionGapRatio_zero]
    have hn : (n : ℂ) ≠ 0 := by exact_mod_cast n.pos.ne'
    have hp : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [hn,hp]
    ring
  refine ⟨K,hK,hK0,?_⟩
  filter_upwards [hphys,hillHminusLocalGapData_eventually_eq_original h0q h0r n,
    hillHminusLocalActionGapRatio_eventually_eq_physical h0q h0r n] with p hp hpdata hpA
  change A (hillOriginalHminusSource p.val)=hillActionGapRatio p.val p.property.1 p.property.2 (n : ℕ) at hpA
  have hAp : A (hillOriginalHminusSource p.val) ≠ 0 := by
    rw [hpA]
    intro he
    have hh := (hillActionGapRatio_real_positive p.val p.property.1 p.property.2 (n : ℕ) n.property).1
    rw [he,zero_re] at hh
    exact (lt_irrefl 0) hh
  have hI := hillRealGapIntegral_eq_halfLength_sq_mul_ratio p.val p.property.1 p.property.2 (n : ℕ) n.property
  rw [←hpA] at hI
  rw [hp,hpdata.2,hI]
  change _ = _*(C (hillOriginalHminusSource p.val)/(A (hillOriginalHminusSource p.val))^2)
  field_simp [hAp]

end NLS.KdV
