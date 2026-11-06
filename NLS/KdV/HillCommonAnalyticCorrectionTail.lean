import NLS.KdV.HillQuadraticDirichletPhysicalMatching
import NLS.KdV.HillUniformRealGapLocalization
import NLS.KdV.HillUniformDirichletPhysical
import NLS.KdV.HillFilledFreeGapPhysical

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r

theorem exists_hillRegularAbelianCorrection_common_analytic_tail
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ SpectralWeight.one.toCoeff q ∈ U ∧
      ∃ N : ℕ, ∃ hN : 1 ≤ N, ∃ C : ℝ, 0 < C ∧ ∃ β : ℕ → Coeff 2 → ℂ,
        (∀ k : ℕ, N ≤ k → AnalyticOnNhd ℂ (β k) U) ∧
        (∀ p ∈ U, ∀ k : ℕ, N ≤ k → ‖β k p‖ ≤ C/(k : ℝ)^2) ∧
        ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
          SpectralWeight.one.toCoeff r.val ∈ U ∧ ∀ k : ℕ, ∀ hk : N ≤ k,
            β k (SpectralWeight.one.toCoeff r.val)=hillRegularAbelianCorrection r.val r.property.1 r.property.2 n hn k (hN.trans hk) := by
  obtain ⟨G,U,hU,hqU,B,hB,hUB,N0,hN0,C,hC,hG,hcharts,hmatchG⟩ :=
    exists_hillSelectedPsi_common_complex_regular_annulus_chart h0q h0r q hq hr n hn
  obtain ⟨Ns,hNs,hNs0,hsol⟩ := exists_hillRegularGap_bounded_analytic_quadratic_solutions h0q h0r G U B hU hUB N0 C hC.le hcharts
  choose H hHa hHe hHb using hsol
  obtain ⟨Nv,hNv,hvalue⟩ := exists_hillComplexQuadraticDirichletValue_analytic_bound h0q h0r U B C hUB hC.le
  obtain ⟨Nr,hNr,hrootmatch⟩ := exists_hillFilledFreeGapRoot_bounded_real_physical_matching h0q h0r B
  obtain ⟨Ny,hNy,hsymmetric⟩ := exists_hillFreeGap_bounded_real_symmetric_data_matching h0q h0r B
  obtain ⟨Nm,hNm,hmumatch⟩ := exists_hillScaledDirichletRoot_bounded_real_physical_matching h0q h0r (1/16) (by norm_num) (by norm_num) B
  obtain ⟨Nl,hNl,hlocalization⟩ := exists_hillFreeGap_bounded_real_midpoint_halfgap_localization h0q h0r (1/16) (by norm_num) (by norm_num) B
  obtain ⟨Nd,hNd,hmuchart⟩ := exists_hillScaledDirichletRoot_bounded_complex_analytic_chart h0q h0r (1/16) (by norm_num) (by norm_num) B
  let N := Ns+Nv+Nr+Ny+Nm+Nl+Nd+2*n+1
  have hN : 1 ≤ N := by dsimp only [N];omega
  let β : ℕ → Coeff 2 → ℂ := fun k p =>
    if hk : Ns ≤ k then hillComplexQuadraticDirichletValue h0q h0r (H k hk) k p else 0
  have hkS (k : ℕ) (hk : N ≤ k) : Ns ≤ k := by dsimp only [N] at hk;omega
  have hkV (k : ℕ) (hk : N ≤ k) : Nv ≤ k := by dsimp only [N] at hk;omega
  refine ⟨U,hU,hqU,N,hN,9*Real.pi^3*C/4,by positivity,β,?_,?_,?_⟩
  · intro k hk
    have hh := (hvalue k (hkV k hk) (H k (hkS k hk)) (hHa k (hkS k hk)) (hHb k (hkS k hk))).1
    simpa only [β,dif_pos (hkS k hk)] using hh
  · intro p hp k hk
    have hh := (hvalue k (hkV k hk) (H k (hkS k hk)) (hHa k (hkS k hk)) (hHb k (hkS k hk))).2 p hp
    simpa only [β,dif_pos (hkS k hk)] using hh
  · filter_upwards [hmatchG] with r hrG
    refine ⟨hrG.1,?_⟩
    intro k hk
    have hkr : Nr ≤ k := by dsimp only [N] at hk;omega
    have hky : Ny ≤ k := by dsimp only [N] at hk;omega
    have hkm : Nm ≤ k := by dsimp only [N] at hk;omega
    have hkl : Nl ≤ k := by dsimp only [N] at hk;omega
    have hkd : Nd ≤ k := by dsimp only [N] at hk;omega
    have hkn : k≠n := by dsimp only [N] at hk;omega
    have hk1 : 1 ≤ k := hN.trans hk
    have hpB : ‖SpectralWeight.one.toCoeff r.val‖ ≤ B :=
      (show ‖SpectralWeight.one.toCoeff r.val‖ < B by simpa only [mem_ball,dist_zero_right] using hUB hrG.1).le
    have hJ : AnalyticOnNhd ℂ (fun E => H k (hkS k hk) (E,SpectralWeight.one.toCoeff r.val))
        (ball (hillRealGapCenter 0 h0q h0r k : ℂ)
          (3*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/4)) := by
      intro E hE
      exact (hHa k (hkS k hk) (E,SpectralWeight.one.toCoeff r.val) ⟨hE,hrG.1⟩).comp
        (f := fun z : ℂ => (z,SpectralWeight.one.toCoeff r.val)) (analyticAt_id.prod analyticAt_const)
    obtain ⟨hM,hS⟩ := hsymmetric r.val r.property.1 r.property.2 hpB k hky
    obtain ⟨hτ,hδ⟩ := hlocalization r.val r.property.1 r.property.2 hpB k hkl
    have hR : 0 < hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k :=
      add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1 (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
    have hmuK : hillScaledDirichletRoot h0q h0r (1/16) k (SpectralWeight.one.toCoeff r.val) ∈
        closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
          (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) :=
      closedBall_subset_closedBall (by linarith : (1/16)*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) ≤
        hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)
        (ball_subset_closedBall (((hmuchart k hkd).2 _ hpB).1))
    have hh := hillComplexQuadraticDirichletValue_eq_physical_of_data h0q h0r r.val r.property.1 r.property.2
      n k hn hk1 hkn G (H k (hkS k hk)) hJ (hHe k (hkS k hk) _ hrG.1) hrG.2
      (hrootmatch r.val r.property.1 r.property.2 hpB k hkr) hM hS
      (hmumatch r.val r.property.1 r.property.2 hpB k hkm) hmuK (by linarith) (by linarith)
    simpa only [β,dif_pos (hkS k hk)] using hh

end NLS.KdV
