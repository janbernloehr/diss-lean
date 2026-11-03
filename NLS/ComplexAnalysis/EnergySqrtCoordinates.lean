import NLS.ComplexAnalysis.QuadraticEnergySheet
import NLS.ComplexAnalysis.PiecewiseLoopLocalMap

/-! Local smooth square-root frequency coordinates for translated
energy. The exact derivative is derived from the squared identity,
retaining the physical energy shift and the nonzero root condition. -/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

def energyFrequency (c E : ℂ) : ℂ := Complex.sqrt (E+c)

def energyFrequencyDomain (c : ℂ) : Set ℂ := {E | E+c ∈ slitPlane}

theorem energyFrequencyDomain_open (c : ℂ) : IsOpen (energyFrequencyDomain c) :=
  isOpen_slitPlane.preimage (continuous_id.add continuous_const)

theorem analyticOnNhd_energyFrequency (c : ℂ) : AnalyticOnNhd ℂ (energyFrequency c) (energyFrequencyDomain c) := by
  intro E hE
  exact (Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds hE)).comp
    (f := fun z : ℂ => z+c) (analyticAt_id.add analyticAt_const)

theorem contDiffOn_energyFrequency (c : ℂ) : ContDiffOn ℝ 2 (energyFrequency c) (energyFrequencyDomain c) := by
  intro E hE
  have h : AnalyticAt ℝ (energyFrequency c) E := (analyticOnNhd_energyFrequency c E hE).restrictScalars
  exact h.contDiffAt.contDiffWithinAt

theorem energyFrequency_sq (c E : ℂ) : (energyFrequency c E)^2 = E+c := complex_sqrt_sq _

theorem energyFrequency_ne_zero (c E : ℂ) (hE : E ∈ energyFrequencyDomain c) : energyFrequency c E ≠ 0 := by
  intro he
  have h := energyFrequency_sq c E
  rw [he,zero_pow (by norm_num : (2:ℕ) ≠ 0)] at h
  exact slitPlane_ne_zero hE h.symm

theorem hasDerivAt_energyFrequency (c E : ℂ) (hE : E ∈ energyFrequencyDomain c) :
    HasDerivAt (energyFrequency c) (1/(2*energyFrequency c E)) E := by
  have hd := (analyticOnNhd_energyFrequency c E hE).differentiableAt.hasDerivAt
  have hs := hd.pow 2
  have hsfun : energyFrequency c ^ 2 = (fun z : ℂ => z+c) := funext (energyFrequency_sq c)
  rw [hsfun] at hs
  have he : 2*energyFrequency c E*deriv (energyFrequency c) E = 1 := by
    simpa using! hs.unique ((hasDerivAt_id E).add_const c)
  have hn := energyFrequency_ne_zero c E hE
  have hder : deriv (energyFrequency c) E = 1/(2*energyFrequency c E) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hn)).mpr
    linear_combination he
  rw [← hder]
  exact hd

def energyFrequencyDisk (c a : ℂ) (R : ℝ) : Set ℂ :=
  energyFrequencyDomain c ∩ energyFrequency c ⁻¹' Metric.ball a R

theorem energyFrequencyDisk_open (c a : ℂ) (R : ℝ) : IsOpen (energyFrequencyDisk c a R) :=
  (analyticOnNhd_energyFrequency c).continuousOn.isOpen_inter_preimage
    (energyFrequencyDomain_open c) Metric.isOpen_ball

end NLS.ComplexAnalysis
