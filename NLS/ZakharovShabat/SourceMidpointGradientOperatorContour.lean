import NLS.ZakharovShabat.SourceMidpointGradientTail
import NLS.ComplexAnalysis.BilinearCircleIntegral
import NLS.SequenceSpaces.PowerDecaySummability

/-! # Operator-valued contours for the actual midpoint derivative

The quotient-weighted source derivative of the discriminant is a continuous
linear functional. Its contour integral recovers the full midpoint Fréchet
derivative, and the normalized contour estimate bounds its operator norm.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The full source Fréchet derivative of the discriminant is entire in the
spectral parameter, in the operator norm topology. -/
theorem analyticOnNhd_sourceDiscriminantFDeriv
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    AnalyticOnNhd ℂ (fun z : ℂ => fderiv ℂ
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z) φ) univ := by
  let F : ℂ × CoeffPair p → ℂ := fun t => canonicalDiscriminant hp (periodOnePotential t.2) t.1
  have hF : AnalyticOnNhd ℂ F univ := analyticOnNhd_canonicalDiscriminant_periodOne hp hp1
  let pre : ((ℂ × CoeffPair p) →L[ℂ] ℂ) →L[ℂ] (CoeffPair p →L[ℂ] ℂ) :=
    (ContinuousLinearMap.compL ℂ (CoeffPair p) (ℂ × CoeffPair p) ℂ).flip
      (ContinuousLinearMap.inr ℂ ℂ (CoeffPair p))
  have hjoint := pre.comp_analyticOnNhd hF.fderiv
  intro z _
  have hsection := (hjoint (z,φ) (mem_univ _)).comp
    (f := fun w : ℂ => (w,φ)) (analyticAt_id.prod analyticAt_const)
  convert hsection using 1
  funext w
  exact fderiv_source_section_eq_joint F w φ (hF (w,φ) (mem_univ _)).differentiableAt

/-- The actual quotient-weighted source discriminant derivative in G.7. -/
def sourceMidpointContourIntegrand (hp : p ≠ ⊤) (φ : CoeffPair p) (z : ℂ) : CoeffPair p →L[ℂ] ℂ :=
  (canonicalDiscriminant hp (periodOnePotential φ) z/
    ((canonicalDiscriminant hp (periodOnePotential φ) z)^2-4)) •
    fderiv ℂ (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z) φ

/-- Evaluation of the operator integrand gives the literal directional integrand. -/
theorem sourceMidpointContourIntegrand_apply
    (hp : p ≠ ⊤) (φ h : CoeffPair p) (z : ℂ) :
    sourceMidpointContourIntegrand hp φ z h =
      canonicalDiscriminant hp (periodOnePotential φ) z*
        ((fderiv ℂ (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h)/
        ((canonicalDiscriminant hp (periodOnePotential φ) z)^2-4) := by
  simp only [sourceMidpointContourIntegrand,smul_apply,smul_eq_mul]
  ring

/-- Absence of characteristic zeros on a circle makes the full operator
integrand continuous and hence integrable there. -/
theorem circleIntegrable_sourceMidpointContourIntegrand
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hne : ∀ z ∈ sphere c r, (canonicalDiscriminant hp (periodOnePotential φ) z)^2-4 ≠ 0) :
    CircleIntegrable (sourceMidpointContourIntegrand hp φ) c r := by
  have hΔ : ContinuousOn (canonicalDiscriminant hp (periodOnePotential φ)) (sphere c r) :=
    (analyticOnNhd_canonicalDiscriminant hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ)).continuousOn.mono (subset_univ _)
  have hD := (analyticOnNhd_sourceDiscriminantFDeriv hp hp1 φ).continuousOn.mono
    (subset_univ (sphere c r))
  exact ((hΔ.div ((hΔ.pow 2).sub continuousOn_const) hne).smul hD).circleIntegrable hr

/-- A directional midpoint contour identity determines the full continuous
linear functional, with the contour integral taken in operator norm. -/
theorem source_midpoint_fderiv_eq_operator_contour
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hne : ∀ z ∈ sphere c r, (canonicalDiscriminant hp (periodOnePotential φ) z)^2-4 ≠ 0)
    (hformula : ∀ h : CoeffPair p,
      (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ) h =
      -(2*Real.pi*I : ℂ)⁻¹ * (∮ z in C(c,r),
        canonicalDiscriminant hp (periodOnePotential φ) z*
          ((fderiv ℂ (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h)/
          ((canonicalDiscriminant hp (periodOnePotential φ) z)^2-4))) :
    fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ =
      -(2*Real.pi*I : ℂ)⁻¹ • (∮ z in C(c,r), sourceMidpointContourIntegrand hp φ z) := by
  ext h
  rw [hformula]
  have heval := map_circleIntegral (ContinuousLinearMap.apply ℂ ℂ h)
    (circleIntegrable_sourceMidpointContourIntegrand hp hp1 φ c r hr hne)
  simp only [smul_apply,smul_eq_mul]
  congr 1
  simpa only [ContinuousLinearMap.apply_apply,sourceMidpointContourIntegrand_apply] using heval.symm

/-- One neighborhood and cutoff give the full operator-valued formula for
all distant indices, together with the radius-times-supremum norm estimate. -/
theorem exists_local_source_midpoint_fderiv_tail_contour_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (hφ : φ ∈ realTypeSourceLocus p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ ∃ N : ℕ,
      ∀ ψ ∈ U, ∀ n : ℤ, N < n.natAbs →
      (∀ z ∈ sphere ((Real.pi : ℂ)*n) (Real.pi/4),
        (canonicalDiscriminant hp (periodOnePotential ψ) z)^2-4 ≠ 0) ∧
      (fderiv ℂ (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) n) ψ =
        -(2*Real.pi*I : ℂ)⁻¹ • (∮ z in C((Real.pi : ℂ)*n,Real.pi/4),
          sourceMidpointContourIntegrand hp ψ z)) ∧
      ∀ B : ℝ, (∀ z ∈ sphere ((Real.pi : ℂ)*n) (Real.pi/4),
        ‖sourceMidpointContourIntegrand hp ψ z‖ ≤ B) →
        ‖fderiv ℂ (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
          (periodOnePotential χ) (periodOnePotential_mem χ) n) ψ‖ ≤ (Real.pi/4)*B := by
  obtain ⟨U,hU,hφU,N,h⟩ := exists_local_source_midpoint_gradient_tail_contour hp hp1 φ hφ
  refine ⟨U,hU,hφU,N,?_⟩
  intro ψ hψ n hn
  obtain ⟨hne,hformula⟩ := h ψ hψ n hn
  have hop := source_midpoint_fderiv_eq_operator_contour hp hp1 ψ n _ _ (by positivity) hne hformula
  refine ⟨hne,hop,?_⟩
  intro B hB
  rw [hop]
  simpa only [norm_smul,norm_inv,norm_neg] using
    circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by positivity) hB

/-- A summable operator integrand majorant on the distant circles yields
summability of the actual midpoint derivatives, with arbitrary finite heads.
Identification of a physical Fourier majorant with this operator majorant is
separate from this contour transfer. -/
theorem memlp_real_source_midpoint_fderiv_of_contour_majorant
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (hφ : φ ∈ realTypeSourceLocus p)
    (s : ℝ) (hs : 0 < s) (b : ℤ → ℝ) (hb : Memℓp b (ENNReal.ofReal s)) (N₀ : ℕ)
    (hbound : ∀ n : ℤ, N₀ ≤ n.natAbs →
      ∀ z ∈ sphere ((Real.pi : ℂ)*n) (Real.pi/4), ‖sourceMidpointContourIntegrand hp φ z‖ ≤ b n) :
    Memℓp (fun n : ℤ => fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ) (ENNReal.ofReal s) := by
  obtain ⟨U,_,hφU,N,h⟩ := exists_local_source_midpoint_fderiv_tail_contour_bound hp hp1 φ hφ
  apply memlp_of_natAbs_eventual_bound s hs _ (fun n => (Real.pi/4)*b n)
    (hb.const_mul (Real.pi/4)) (max (N+1) N₀)
  intro n hn
  have hN : N < n.natAbs := by omega
  have hN₀ : N₀ ≤ n.natAbs := le_trans (le_max_right _ _) hn
  exact (h φ hφU n hN).2.2 (b n) (hbound n hN₀)

end NLS.ZakharovShabat
