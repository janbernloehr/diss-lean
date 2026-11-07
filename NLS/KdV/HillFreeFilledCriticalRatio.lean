import NLS.KdV.HillFreeMiuraGapData
import NLS.KdV.HillFreeMiuraCriticalRatio
import NLS.ComplexAnalysis.NonrealContinuousIdentity
import NLS.ZakharovShabat.SourceCriticalRootGapNeighborhood

/-! The exact filled free critical/root quotient at EVERY positive
actual Miura midpoint. Nonreal physical sheet agreement and continuity
fix the value, including its sign, at the collapsed gap itself. -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV.HillHminusMiuraGapBall

theorem freeCriticalRootRatio_value (B : HillHminusMiuraGapBall)
    (h0 : (0 : PeriodOneHminusOne) ∈ B.source) (n : ℕ+) :
    sourceCriticalRootRatioExtension (by norm_num) (by norm_num) (n:ℕ)
      (hillMiuraDiagonal (B.actionBall.lift 0)) (B.freeFrequencyMidpoint n) =
        -I*B.freeFrequencyMidpoint n/((Real.pi:ℂ)*n) := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  let u : PeriodOneRealL2 := ⟨B.actionBall.lift 0,B.actionBall.lift_real 0 h0 hr⟩
  let φ := hillMiuraDiagonal u.val
  let τ := B.freeFrequencyMidpoint n
  let Ω := sourceStandardRootOmittedDomain (by norm_num) (by norm_num) φ (n:ℕ)
  let E := sourceCriticalRootRatioExtension (by norm_num) (by norm_num) (n:ℕ) φ
  let H : ℂ → ℂ := fun z => sqrt (z^2-(B.actionBall.shift:ℂ))
  have hreal : IsRealType (CoeffPair.toMax 2 φ) := (hillMiuraRealSource u).property
  have hgap : sourcePeriodicGapDisplacement (by norm_num) (by norm_num) φ (n:ℕ)=0 := B.freeSourceGap_zero h0 n
  obtain ⟨W,_,hWreal,hEdata⟩ := exists_global_sourceCriticalRootRatio_analytic_of_zeroGap
    (p := 2) (by norm_num) (by norm_num)
  have hE : AnalyticOnNhd ℂ E Ω := (hEdata φ (hWreal hreal) (n:ℕ) hgap).1
  have hΩ : IsOpen Ω := isOpen_sourceStandardRootOmittedDomain_of_realType
    (by norm_num) (by norm_num) φ hreal (n:ℕ)
  have hτΩ : τ ∈ Ω := by
    obtain ⟨V,_,_,hVreal,hdisjoint⟩ := exists_global_source_disjoint_periodicSegments
      (p := 2) (by norm_num) (by norm_num)
    intro m hmn hm
    exact Set.disjoint_left.mp (hdisjoint φ (hVreal hreal) (n:ℕ) m (Ne.symm hmn))
      (sourcePeriodicMidpoint_mem_segment (by norm_num) (by norm_num) φ (n:ℕ)) hm
  let U := Ω ∩ ({z : ℂ | 0 < z.re} ∩ {z : ℂ | z^2-(B.actionBall.shift:ℂ) ∈ slitPlane})
  have hU : IsOpen U := hΩ.inter ((isOpen_lt continuous_const continuous_re).inter
    (isOpen_slitPlane.preimage (show Continuous (fun z : ℂ => z^2-(B.actionBall.shift:ℂ)) by fun_prop)))
  have hpn : 0 < (((Real.pi:ℂ)*n).re) := by
    simp only [mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,natCast_re]
    positivity
  have hτU : τ ∈ U := by
    refine ⟨hτΩ,B.freeFrequencyMidpoint_pos h0 n,?_⟩
    change (B.freeFrequencyMidpoint n)^2-(B.actionBall.shift:ℂ) ∈ slitPlane
    rw [B.freeFrequencyMidpoint_energy h0 n]
    exact sq_mem_slitPlane_of_re_pos _ hpn
  have hH : AnalyticOnNhd ℂ H U := by
    intro z hz
    exact (Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds hz.2.2)).comp
      (f := fun w : ℂ => w^2-(B.actionBall.shift:ℂ)) ((analyticAt_id.pow 2).sub analyticAt_const)
  have hf : ContinuousOn (fun z => E z*H z) U :=
    (hE.continuousOn.mono inter_subset_left).mul hH.continuousOn
  have hg : ContinuousOn (fun z : ℂ => -I*z) U := by fun_prop
  have heoff (z : ℂ) (hz : z ∈ U) (hzi : z.im ≠ 0) : E z*H z = -I*z := by
    have hi : periodOneMiura u.val = periodOneL2Inclusion (lp.single 2 0 (B.actionBall.shift:ℂ)) := by
      simpa only [zero_add] using B.actionBall.image 0 h0
    have hene : z^2-(B.actionBall.shift:ℂ) ≠ 0 := fun he =>
      shifted_square_im_ne_zero z B.actionBall.shift hz.2.1 hzi (by rw [he]; rfl)
    have hw : H z ≠ 0 := by
      intro he
      change sqrt (z^2-(B.actionBall.shift:ℂ))=0 at he
      apply hene
      rw [← complex_sqrt_sq (z^2-(B.actionBall.shift:ℂ)),he]
      simp
    change sourceCriticalRootRatioExtension (by norm_num) (by norm_num) (n:ℕ)
      (hillMiuraDiagonal u.val) z*H z = _
    rw [sourceCriticalRootRatioExtension_shifted_free_nonreal u B.actionBall.shift hi (n:ℕ) hgap z hz.2.1 hzi]
    exact div_mul_cancel₀ _ hw
  have he := NLS.ComplexAnalysis.ContinuousOn.eqOn_of_nonreal hU hf hg heoff hτU
  have hs : H τ=(Real.pi:ℂ)*n := by
    change sqrt ((B.freeFrequencyMidpoint n)^2-(B.actionBall.shift:ℂ))=_
    rw [B.freeFrequencyMidpoint_energy h0 n,sqrt_sq_of_re_pos _ hpn]
  change E τ*H τ = -I*τ at he
  rw [hs] at he
  exact (eq_div_iff (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by exact_mod_cast n.ne_zero))).2 he

end NLS.KdV.HillHminusMiuraGapBall
