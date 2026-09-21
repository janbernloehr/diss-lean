import NLS.ZakharovShabat.RealSpectralPairSigns
import NLS.ZakharovShabat.CanonicalPeriodicGapOrder
import NLS.ZakharovShabat.PeriodicEndpointProducts

/-!
# The sign of the discriminant square on real gaps
Locally uniform convergence of the literal paired cutoffs transfers their
signs to the actual discriminant square. This includes all central indices
and collapsed gaps without any asymptotic cutoff restriction.
-/

noncomputable section
open Set Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual real cutoffs converge to the real discriminant square minus four. -/
theorem tendsto_re_canonicalPeriodicCutoffs (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (x : ℝ) :
    Tendsto (fun N => (spectralPairPartialProduct (canonicalPeriodicLeft hp hp1 φ heven)
      (canonicalPeriodicRight hp hp1 φ heven) x N).re) atTop
      (𝓝 ((canonicalDiscriminant hp φ x).re^2-4)) := by
  have hl := (canonicalPeriodicEndpoints_spec hp hp1 φ heven).1
  have h := (tendstoLocallyUniformlyOn_entireSpectralPairProduct hp _ _ hl.left_displacement
    hl.right_displacement).tendsto_at (mem_univ (x : ℂ))
  rw [canonicalPeriodicEndpoints_product hp hp1 φ heven,
    canonicalPeriodic_eq_discriminant_sq_sub_four_finite hp hp1 φ heven] at h
  have hre := continuous_re.continuousAt.tendsto.comp h
  simpa [Function.comp_def,sub_re,pow_two,mul_re,
    canonicalDiscriminant_im_eq_zero_of_realType hp hp1 φ heven hreal,mul_zero,sub_zero] using hre

/-- A real point outside a canonical gap gives a nonnegative paired numerator. -/
theorem canonicalPeriodicPairNumerator_nonneg_of_notMem_gap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (x : ℝ) (n : ℤ)
    (hx : x ∉ Icc (canonicalPeriodicLeft hp hp1 φ heven n).re (canonicalPeriodicRight hp hp1 φ heven n).re) :
    0 ≤ ((canonicalPeriodicLeft hp hp1 φ heven n).re-x)*((canonicalPeriodicRight hp hp1 φ heven n).re-x) := by
  have horder := re_le_of_complexLexLE ((canonicalPeriodicEndpoints_spec hp hp1 φ heven).2.1 n)
  simp only [mem_Icc,not_and_or,not_le] at hx
  rcases hx with hx | hx
  · exact mul_nonneg (by linarith) (by linarith)
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)

/-- On every actual real gap the square of the discriminant is at least four. -/
theorem discriminant_re_sq_ge_four_of_mem_canonicalGap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ) (x : ℝ)
    (hx : x ∈ Icc (canonicalPeriodicLeft hp hp1 φ heven n).re (canonicalPeriodicRight hp hp1 φ heven n).re) :
    4 ≤ (canonicalDiscriminant hp φ x).re^2 := by
  have hpair : ((canonicalPeriodicLeft hp hp1 φ heven n).re-x)*
      ((canonicalPeriodicRight hp hp1 φ heven n).re-x) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.1) (sub_nonneg.mpr hx.2)
  have hother (k : ℤ) (hk : k ≠ n) := canonicalPeriodicPairNumerator_nonneg_of_notMem_gap hp hp1 φ heven x k
    (fun hmem => Set.disjoint_left.mp (canonicalPeriodicGaps_disjoint hp hp1 φ heven hreal hk) hmem hx)
  have hlim := tendsto_re_canonicalPeriodicCutoffs hp hp1 φ heven hreal x
  have hnonneg : 0 ≤ (canonicalDiscriminant hp φ x).re^2-4 := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop n.natAbs] with N hN
    exact spectralPairPartialProduct_re_nonneg _ _
      (fun k => (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 φ heven hreal k).1)
      (fun k => (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 φ heven hreal k).2) x n hpair hother N hN
  linarith

/-- Outside the union of all real gaps the discriminant square is at most four. -/
theorem discriminant_re_sq_le_four_of_outside_canonicalGaps (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (x : ℝ)
    (hx : ∀ n : ℤ, x ∉ Icc (canonicalPeriodicLeft hp hp1 φ heven n).re (canonicalPeriodicRight hp hp1 φ heven n).re) :
    (canonicalDiscriminant hp φ x).re^2 ≤ 4 := by
  have hnonpos : (canonicalDiscriminant hp φ x).re^2-4 ≤ 0 := by
    apply le_of_tendsto (tendsto_re_canonicalPeriodicCutoffs hp hp1 φ heven hreal x)
    filter_upwards [] with N
    exact spectralPairPartialProduct_re_nonpos _ _
      (fun k => (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 φ heven hreal k).1)
      (fun k => (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 φ heven hreal k).2) x
      (fun k => canonicalPeriodicPairNumerator_nonneg_of_notMem_gap hp hp1 φ heven x k (hx k)) N
  linarith

end NLS.ZakharovShabat
