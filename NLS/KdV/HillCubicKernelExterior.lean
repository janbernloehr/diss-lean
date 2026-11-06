import NLS.KdV.HillCubicKernelFilledDomain
import NLS.KdV.HillFiniteGapExterior

/-! # Exact actual cubic exterior periods for finite-gap Hill sources -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem HillFiniteGap.exists_exterior_subset_cubic_filled
    (hfg : HillFiniteGap q hq hr) (n : ℕ) :
    ∃ R : ℝ, 0<R ∧ {E : ℂ | R<‖E‖}⊆hillCubicFilledDomain q hq hr n := by
  obtain ⟨R₀,hR₀,hsub⟩ := HillFiniteGap.exists_exterior_subset_filled_square q hq hr hfg
  let a := hillRealLabels q hq hr (2*n-1)
  let b := hillRealLabels q hq hr (2*n)
  let B := |a|+|b|+1
  have hseg : segment ℝ (a:ℂ) (b:ℂ)⊆ball (0:ℂ) B := by
    apply (convex_ball _ _).segment_subset
    · rw [mem_ball_zero_iff,norm_real,Real.norm_eq_abs]
      dsimp only [B]
      linarith [abs_nonneg b]
    · rw [mem_ball_zero_iff,norm_real,Real.norm_eq_abs]
      dsimp only [B]
      linarith [abs_nonneg a]
  refine ⟨max R₀ B,hR₀.trans_le (le_max_left _ _),?_⟩
  intro E hE
  change max R₀ B<‖E‖ at hE
  refine ⟨hsub (show R₀<‖E‖ from (le_max_left _ _).trans_lt hE),?_⟩
  intro hEs
  have hnorm : ‖E‖<B := mem_ball_zero_iff.mp (hseg hEs)
  exact (not_lt_of_ge (le_max_right R₀ B)) (hE.trans hnorm)

/-- The genuine cubic integrand is circle integrable at every large
radius and its outer periods are exactly independent of that radius. -/
theorem HillFiniteGap.exists_cubic_exterior_and_periods
    (hfg : HillFiniteGap q hq hr) (n : ℕ) (hn : 1≤n) :
    ∃ R : ℝ, 0<R ∧
      AnalyticOnNhd ℂ (hillL2FilledCubicKernel q (hillAbelianSelectedGlobalPsi q hq hr n hn))
        {E : ℂ | R<‖E‖} ∧
      ∀ r : ℝ, R<r →
        CircleIntegrable (hillL2CubicKernel q (hillAbelianSelectedGlobalPsi q hq hr n hn)) 0 r ∧
        ∀ s : ℝ, R<s →
          (∮ E in C(0,r), hillL2CubicKernel q (hillAbelianSelectedGlobalPsi q hq hr n hn) E)=
            ∮ E in C(0,s), hillL2CubicKernel q (hillAbelianSelectedGlobalPsi q hq hr n hn) E := by
  obtain ⟨R,hR,hsub⟩ := HillFiniteGap.exists_exterior_subset_cubic_filled q hq hr hfg n
  let P := hillAbelianSelectedGlobalPsi q hq hr n hn
  let G := hillL2FilledCubicKernel q P
  have hP : AnalyticOnNhd ℂ P univ := analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn
  have ha : AnalyticOnNhd ℂ G {E : ℂ | R<‖E‖} :=
    (analyticOnNhd_hillL2FilledCubicKernel q hq hr n hn).mono hsub
  have hi (r s : ℝ) (hrR : R<r) (hrs : r≤s) :
      (∮ E in C(0,s), G E)=∮ E in C(0,r), G E := by
    have hA : AnalyticOnNhd ℂ G (closedBall 0 s \ ball 0 r) := ha.mono (by
      intro E hE
      have hnorm : r≤‖E‖ := by
        by_contra hh
        exact hE.2 (mem_ball_zero_iff.mpr (lt_of_not_ge hh))
      exact hrR.trans_le hnorm)
    exact Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      (hR.trans hrR) hrs countable_empty hA.continuousOn
      (fun E hE => (hA E ⟨ball_subset_closedBall hE.1.1,
        fun h => hE.1.2 (ball_subset_closedBall h)⟩).differentiableAt)
  refine ⟨R,hR,ha,?_⟩
  intro r hrR
  have hrp : 0<r := hR.trans hrR
  have hGi : CircleIntegrable G 0 r := (ha.continuousOn.mono (by
    intro E hE
    have he : ‖E‖=r := by simpa only [mem_sphere_iff_norm,sub_zero] using hE
    change R<‖E‖
    rw [he]
    exact hrR)).circleIntegrable hrp.le
  refine ⟨(circleIntegrable_hillL2FilledCubicKernel_iff q hq hr P hP r hrp).mp hGi,?_⟩
  intro s hsR
  rw [← circleIntegral_hillL2FilledCubicKernel_eq q hq hr P hP r hrp,
    ← circleIntegral_hillL2FilledCubicKernel_eq q hq hr P hP s (hR.trans hsR)]
  by_cases hrs : r≤s
  · exact (hi r s hrR hrs).symm
  · exact hi s r hsR (le_of_not_ge hrs)

end NLS.KdV
