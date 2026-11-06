import NLS.KdV.HillCubicKernelLocalContinuation
import NLS.ComplexAnalysis.DenseAnalyticExtension
import NLS.ComplexAnalysis.DenseNonreal
import NLS.ComplexAnalysis.NonrealCircleCongruence

/-! # The actual cubic Hill kernel with ground and nonselected closed gaps filled -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The selected own gap remains a hole, even when it is closed. -/
def hillCubicFilledDomain (n : ℕ) : Set ℂ :=
  hillL2FilledSquareDomain q hq hr \ segment ℝ
    (hillRealLabels q hq hr (2*n-1) : ℂ) (hillRealLabels q hq hr (2*n) : ℂ)

/-- A single continuation chosen by the actual nonreal spectral data. -/
def hillL2FilledCubicKernel (P : ℂ → ℂ) : ℂ → ℂ :=
  denseLimitExtension (hillL2CubicKernel q P) {E : ℂ | E.im≠0}

theorem analyticOnNhd_hillL2CubicKernel_realCut
    (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ) :
    AnalyticOnNhd ℂ (hillL2CubicKernel q P) (hillL2RealCutDomain q hq hr) := by
  intro E hE
  have hF := analyticOnNhd_hillL2RealCutPrimitive q hq hr E hE
  have hR : AnalyticAt ℂ (hillL2RealCutRoot (SpectralWeight.one.toCoeff q)) E :=
    analyticAt_const.mul (Complex.analyticAt_sinh.comp hF)
  exact ((hF.pow 3).mul (hP E (mem_univ _))).div hR
    (hillL2RealCutRoot_ne_zero q hq hr E hE)

theorem hillL2FilledCubicKernel_eq_on_realCut
    (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ) :
    EqOn (hillL2FilledCubicKernel q P) (hillL2CubicKernel q P) (hillL2RealCutDomain q hq hr) := by
  exact denseLimitExtension_eqOn_local _ _ _ _ dense_complex_nonreal
    (isOpen_hillL2RealCutDomain q hq hr)
    (analyticOnNhd_hillL2CubicKernel_realCut q hq hr P hP).continuousOn (fun _ _ => rfl)

theorem analyticOnNhd_hillL2FilledCubicKernel
    (n : ℕ) (hn : 1≤n) :
    AnalyticOnNhd ℂ (hillL2FilledCubicKernel q (hillAbelianSelectedGlobalPsi q hq hr n hn))
      (hillCubicFilledDomain q hq hr n) := by
  let P := hillAbelianSelectedGlobalPsi q hq hr n hn
  have hP : AnalyticOnNhd ℂ P univ := analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn
  apply denseLimitExtension_analyticOnNhd _ _ _ dense_complex_nonreal
  intro E hE
  have hnot := hE.2
  rcases hE.1 with hcut | hground | ⟨k,hk,hclosed,hre⟩
  · exact ⟨hillL2RealCutDomain q hq hr,hillL2CubicKernel q P,
      isOpen_hillL2RealCutDomain q hq hr,hcut,
      analyticOnNhd_hillL2CubicKernel_realCut q hq hr P hP,fun _ _ => rfl⟩
  · by_cases hi : E.im≠0
    · exact ⟨hillL2RealCutDomain q hq hr,hillL2CubicKernel q P,
        isOpen_hillL2RealCutDomain q hq hr,Or.inl hi,
        analyticOnNhd_hillL2CubicKernel_realCut q hq hr P hP,fun _ _ => rfl⟩
    have hEC : E=(E.re : ℂ) := by apply Complex.ext <;> simp [not_ne_iff.mp hi]
    simpa only [← hEC] using exists_hillL2CubicKernel_ground_chart q hq hr P hP E.re hground
  · by_cases hi : E.im≠0
    · exact ⟨hillL2RealCutDomain q hq hr,hillL2CubicKernel q P,
        isOpen_hillL2RealCutDomain q hq hr,Or.inl hi,
        analyticOnNhd_hillL2CubicKernel_realCut q hq hr P hP,fun _ _ => rfl⟩
    have hEC : E=(hillRealLabels q hq hr (2*k-1) : ℂ) := by
      apply Complex.ext <;> simp [hre,not_ne_iff.mp hi]
    have hkn : k≠n := by
      intro he
      subst k
      exact hnot (hEC ▸ left_mem_segment ℝ _ _)
    simpa only [← hEC] using exists_hillL2CubicKernel_collapsed_chart q hq hr n k hn hk hkn hclosed

include hq hr in
/-- Filling the real cuts changes no centered circle integral. -/
theorem circleIntegral_hillL2FilledCubicKernel_eq
    (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ) (r : ℝ) (hrp : 0<r) :
    (∮ E in C(0,r), hillL2FilledCubicKernel q P E)=
      ∮ E in C(0,r), hillL2CubicKernel q P E := by
  apply circleIntegral.circleIntegral_congr_codiscreteWithin ?_ hrp.ne'
  rw [abs_of_pos hrp]
  exact eventuallyEq_circle_of_eq_nonreal _ _ r hrp (fun E hE =>
    hillL2FilledCubicKernel_eq_on_realCut q hq hr P hP (Or.inl hE))

include hq hr in
/-- The actual and filled cubic kernels have the same circle integrability. -/
theorem circleIntegrable_hillL2FilledCubicKernel_iff
    (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ) (r : ℝ) (hrp : 0<r) :
    CircleIntegrable (hillL2FilledCubicKernel q P) 0 r ↔ CircleIntegrable (hillL2CubicKernel q P) 0 r := by
  apply circleIntegrable_congr_codiscreteWithin
  rw [abs_of_pos hrp]
  exact eventuallyEq_circle_of_eq_nonreal _ _ r hrp (fun E hE =>
    hillL2FilledCubicKernel_eq_on_realCut q hq hr P hP (Or.inl hE))

end NLS.KdV
