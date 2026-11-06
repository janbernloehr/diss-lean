import NLS.KdV.HillLabelledAbelianInterpolation
import NLS.KdV.HillDirichletFlowResidues

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.LinearVolterra NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillL2DirichletCharacteristic_ne_zero_on_realCutDomain
    (z : ℂ) (hz : z∈hillL2RealCutDomain q hq hr) :
    hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) z≠0 := by
  intro hzero
  have him := hillL2DirichletCharacteristic_zero_real (SpectralWeight.one.toCoeff q) hr z hzero
  rcases hz with hne | ⟨k,hband⟩
  · exact hne him
  · have he : (z.re : ℂ)=z := by
      apply Complex.ext
      · rfl
      · simpa only [ofReal_im] using him.symm
    exact hillL2DirichletCharacteristic_ne_zero_on_open_band q hq hr k z.re hband (by rw [he];exact hzero)

/-- The labelled Abelian expansion may be integrated term by term
against any continuous weight on a circle in the original physical cut
domain. This is the Cauchy-residue sum needed by the action flows. -/
theorem hillLabelledAbelianInterpolation_weighted_contour
    (n : ℕ) (hn : 1≤n) (a : ℂ → ℂ) (c : ℂ) (r : ℝ) (hradius : 0≤r)
    (ha : ContinuousOn a (sphere c r)) (hcircle : sphere c r⊆hillL2RealCutDomain q hq hr) :
    Tendsto (fun N => ∑ j∈Finset.range N,
      (hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr (j+1) (by omega))/
        deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q))
          (hillDirichletEnergy q hq hr (j+1) (by omega)))*
        ∮ z in C(c,r),a z*hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) z/
          (z-(hillDirichletEnergy q hq hr (j+1) (by omega) : ℂ)))
      atTop (𝓝 (∮ z in C(c,r),a z*hillAbelianSelectedGlobalPsi q hq hr n hn z)) := by
  let p := SpectralWeight.one.toCoeff q
  let μ : ℕ → ℂ := fun j => hillDirichletEnergy q hq hr (j+1) (by omega)
  let ψ := hillAbelianSelectedGlobalPsi q hq hr n hn
  let D := hillL2DirichletCharacteristic p
  let b : ℕ → ℂ := fun j => ψ (μ j)/deriv D (μ j)
  let P : ℕ → ℂ → ℂ := fun N z => ∑ j∈Finset.range N,b j/(z-μ j)
  let F : ℕ → ℂ → ℂ := fun N z => a z*D z*P N z
  have hD (z : ℂ) (hz : z∈sphere c r) : D z≠0 :=
    hillL2DirichletCharacteristic_ne_zero_on_realCutDomain q hq hr z (hcircle hz)
  have hne (z : ℂ) (hz : z∈sphere c r) (j : ℕ) : z-μ j≠0 := by
    apply sub_ne_zero.mpr
    intro he
    apply hD z hz
    rw [he]
    exact hillDirichletEnergy_zero q hq hr (j+1) (by omega)
  have hDc : ContinuousOn D (sphere c r) :=
    (analyticOnNhd_hillL2DirichletCharacteristic p).continuousOn.mono (subset_univ _)
  have hkernel (j : ℕ) : CircleIntegrable (fun z => a z*D z/(z-μ j)) c r :=
    ((ha.mul hDc).div (continuousOn_id.sub continuousOn_const) (fun z hz => hne z hz j)).circleIntegrable hradius
  have hF (N : ℕ) : ContinuousOn (F N) (sphere c r) := by
    intro z hz
    have hP : AnalyticAt ℂ (P N) z := by
      apply Finset.analyticAt_fun_sum (Finset.range N)
      intro j _
      exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) (hne z hz j)
    exact ((ha z hz).mul (hDc z hz)).mul hP.continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := ((isCompact_sphere c r).image_of_continuousOn (ha.mul hDc)).isBounded.exists_norm_le
  let B := max C 0+1
  have hB : 0<B := by dsimp only [B];linarith [le_max_right C 0]
  have hbound (z : ℂ) (hz : z∈sphere c r) : ‖a z*D z‖≤B := by
    have hh := hC _ ⟨z,hz,rfl⟩
    change ‖a z*D z‖≤C at hh
    dsimp only [B]
    linarith [le_max_left C 0]
  have hA (z : ℂ) (hz : z∈sphere c r) : ‖z‖≤‖c‖+r := by
    have hh := norm_le_norm_sub_add z c
    rw [show ‖z-c‖=r by simpa only [mem_sphere,dist_eq_norm] using hz] at hh
    linarith
  have hU : TendstoUniformlyOn F (fun z => a z*ψ z) atTop (sphere c r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(hillAbelianSelectedGlobalPsi_dirichlet_labelled_interpolation q hq hr n hn).2
      (‖c‖+r) (ε/B) (div_pos hε hB)] with N hN z hz
    have he : F N z-a z*ψ z=(a z*D z)*(P N z-ψ z/D z) := by
      dsimp only [F]
      field_simp [hD z hz]
    rw [dist_eq_norm,norm_sub_rev,he,norm_mul]
    have hh := hN z (hA z hz) (hD z hz)
    have hm := mul_le_mul_of_nonneg_right (hbound z hz) (norm_nonneg (P N z-ψ z/D z))
    apply hm.trans_lt
    have ht := mul_lt_mul_of_pos_left hh hB
    have hcancel : B*(ε/B)=ε := by field_simp
    rwa [hcancel] at ht
  have ht := hU.tendsto_circleIntegral_of_continuousOn hradius (Eventually.of_forall hF)
  have hsum (N : ℕ) : (∮ z in C(c,r),F N z)=
      ∑ j∈Finset.range N,b j*(∮ z in C(c,r),a z*D z/(z-μ j)) := by
    have he : F N=fun z => ∑ j∈Finset.range N,b j*(a z*D z/(z-μ j)) := by
      funext z
      dsimp only [F,P]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hci (j : ℕ) : CircleIntegrable (fun z : ℂ => b j*(a z*D z/(z-μ j))) c r := by
      exact ((continuousOn_const : ContinuousOn (fun _ : ℂ => b j) (sphere c r)).mul
        ((ha.mul hDc).div (continuousOn_id.sub continuousOn_const) (fun z hz => hne z hz j))).circleIntegrable hradius
    rw [he,circleIntegral.integral_fun_sum (fun j _ => hci j)]
    simp_rw [circleIntegral.integral_const_mul]
  simp_rw [hsum] at ht
  exact ht

end NLS.KdV
