import NLS.ZakharovShabat.SourceDirichletSpectralFlow

/-! # The fixed spectral sheet of the complete actual Hilbert flow

All finite-interval conservation and terminal equations hold on the
constructed global source curve at every real time. No periodic endpoint
or collapsed gap is excluded.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

private theorem exists_interval_zero_time (t : ℝ) :
    ∃ a b : ℝ, (0 : ℝ) ∈ Ioo a b ∧ t ∈ Ioo a b := by
  refine ⟨min t 0-1,max t 0+1,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · linarith [min_le_right t 0]
  · linarith [le_max_right t 0]
  · linarith [min_le_left t 0]
  · linarith [le_max_left t 0]

/-- Every periodic endpoint is fixed throughout the complete flow. -/
theorem canonicalPeriodicEndpoints_sourceDirichletSpectralGlobalCurve
    (k n : ℤ) (φ : realTypeSourceLocus 2) (t : ℝ) :
    canonicalPeriodicLeft (by simp) (by norm_num)
      (periodOnePotential (sourceDirichletSpectralGlobalCurve k φ t))
      (periodOnePotential_mem (sourceDirichletSpectralGlobalCurve k φ t)) n =
      canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ∧
    canonicalPeriodicRight (by simp) (by norm_num)
      (periodOnePotential (sourceDirichletSpectralGlobalCurve k φ t))
      (periodOnePotential_mem (sourceDirichletSpectralGlobalCurve k φ t)) n =
      canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n := by
  obtain ⟨a,b,h0,ht⟩ := exists_interval_zero_time t
  let γ := sourceDirichletSpectralGlobalCurve k φ
  have hzero : γ 0 = φ.val := sourceDirichletSpectralGlobalCurve_zero k φ
  simpa only [hzero] using canonicalPeriodicEndpoints_eq_on_sourceDirichletSpectral_integralCurve
    (by simp) (by norm_num) (by norm_num) k n γ a b
    (fun u _ => sourceDirichletSpectralGlobalCurve_realType k φ u)
    (fun u _ => hasDerivAt_sourceDirichletSpectralGlobalCurve k φ u) t 0 ht h0

/-- Moving one indexed terminal fixes every other Dirichlet root and
terminal anti-discriminant for every real time. -/
theorem other_dirichletTerminals_sourceDirichletSpectralGlobalCurve
    (k m : ℤ) (hmk : m ≠ k) (φ : realTypeSourceLocus 2) (t : ℝ) :
    canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet
      (sourceDirichletSpectralGlobalCurve k φ t) m =
      canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ.val m ∧
    sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet m
      (sourceDirichletSpectralGlobalCurve k φ t) =
      sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet m φ.val := by
  obtain ⟨a,b,h0,ht⟩ := exists_interval_zero_time t
  let γ := sourceDirichletSpectralGlobalCurve k φ
  have hzero : γ 0 = φ.val := sourceDirichletSpectralGlobalCurve_zero k φ
  simpa only [hzero] using other_dirichletTerminals_eq_on_sourceDirichletSpectral_integralCurve
    (by simp) (by norm_num) (by norm_num) k m hmk γ a b
    (fun u _ => sourceDirichletSpectralGlobalCurve_realType k φ u)
    (fun u _ => hasDerivAt_sourceDirichletSpectralGlobalCurve k φ u) t 0 ht h0

/-- The actual selected terminal stays on the original fixed compact
sheet throughout the complete source flow. -/
theorem dirichletTerminal_mem_sourceDirichletSpectralGlobalCurve_fixedSheet
    (k : ℤ) (φ : realTypeSourceLocus 2) (t : ℝ) :
    (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet
      (sourceDirichletSpectralGlobalCurve k φ t) k,
      sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet k
        (sourceDirichletSpectralGlobalCurve k φ t)) ∈
      sourceDirichletSpectralSheet (by simp) (by norm_num) k φ.val := by
  obtain ⟨a,b,h0,ht⟩ := exists_interval_zero_time t
  let γ := sourceDirichletSpectralGlobalCurve k φ
  have hzero : γ 0 = φ.val := sourceDirichletSpectralGlobalCurve_zero k φ
  simpa only [hzero] using dirichletTerminal_mem_fixedSheet_on_sourceDirichletSpectral_integralCurve
    (by simp) (by norm_num) (by norm_num) k γ a b
    (fun u _ => sourceDirichletSpectralGlobalCurve_realType k φ u)
    (fun u _ => hasDerivAt_sourceDirichletSpectralGlobalCurve k φ u) 0 t h0 ht

/-- The actual two-coordinate terminal equation uses the initial
discriminant for every real time, including every periodic terminal. -/
theorem hasDerivAt_dirichletTerminal_sourceDirichletSpectralGlobalCurve
    (k : ℤ) (φ : realTypeSourceLocus 2) (t : ℝ) :
    let μ := fun τ => canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet
      (sourceDirichletSpectralGlobalCurve k φ τ) k;
    let S := fun τ => sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet k
      (sourceDirichletSpectralGlobalCurve k φ τ);
    let Δ := canonicalDiscriminant (by simp) (periodOnePotential φ.val);
    HasDerivAt μ (-S t/2) t ∧ HasDerivAt S (-Δ (μ t)*deriv Δ (μ t)/2) t := by
  obtain ⟨a,b,h0,ht⟩ := exists_interval_zero_time t
  let γ := sourceDirichletSpectralGlobalCurve k φ
  have hzero : γ 0 = φ.val := sourceDirichletSpectralGlobalCurve_zero k φ
  simpa only [hzero] using hasDerivAt_dirichletTerminal_fixedDiscriminant_on_sourceDirichletSpectral_integralCurve
    (by simp) (by norm_num) (by norm_num) k γ a b
    (fun u _ => sourceDirichletSpectralGlobalCurve_realType k φ u)
    (fun u _ => hasDerivAt_sourceDirichletSpectralGlobalCurve k φ u) 0 t h0 ht

end NLS.ZakharovShabat
