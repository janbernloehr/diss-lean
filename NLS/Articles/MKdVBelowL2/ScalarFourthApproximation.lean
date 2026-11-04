import NLS.Articles.MKdVBelowL2.ScalarFourthTrajectory

/-! # Original scalar Fourier approximation and uniqueness of limits

These approximants preserve scalar reality and converge in the physical norm.
The path conclusions use the actual uniform scalar trajectory norm. Agreement
with arbitrary smooth PDE solutions is still required for Theorem 1.1.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Symmetric actual Fourier truncation as a scalar real distribution. -/
def physicalScalarTruncate (N : ℕ) (u : PhysicalScalarRealInput p) : PhysicalScalarRealInput p :=
  (physicalScalarDiagonal (p := p)).symm
    ⟨physicalMKdVTruncate N (physicalScalarPairCLM u),physicalMKdVTruncate_mem N (physicalScalarDiagonal u)⟩

theorem physicalScalarTruncate_pair (N : ℕ) (u : PhysicalScalarRealInput p) :
    physicalScalarPairCLM (physicalScalarTruncate N u) = physicalMKdVTruncate N (physicalScalarPairCLM u) :=
  congrArg Subtype.val ((physicalScalarDiagonal (p := p)).apply_symm_apply _)

/-- Each scalar approximant has finite actual physical Fourier support. -/
theorem physicalScalarTruncate_finite (N : ℕ) (u : PhysicalScalarRealInput p) :
    Coeff.HasFiniteSupport ((PeriodicFourierLebesgue.unweightedCoefficients p) (physicalScalarTruncate N u).val) := by
  have h := (physicalMKdVTruncate_finite N (physicalScalarPairCLM u)).1
  rw [← physicalScalarTruncate_pair] at h
  exact h

theorem tendsto_physicalScalarTruncate (hp : p ≠ ⊤) (u : PhysicalScalarRealInput p) :
    Tendsto (fun N : ℕ => physicalScalarTruncate N u) atTop (𝓝 u) := by
  have h : Tendsto (fun N : ℕ => (⟨physicalMKdVTruncate N (physicalScalarPairCLM u),
      physicalMKdVTruncate_mem N (physicalScalarDiagonal u)⟩ : PhysicalMKdVInput p))
      atTop (𝓝 (physicalScalarDiagonal u)) :=
    tendsto_subtype_rng.mpr (tendsto_physicalMKdVTruncate hp (physicalScalarPairCLM u))
  have hl := (physicalScalarDiagonal (p := p)).symm.continuous.continuousAt.tendsto.comp h
  simpa only [Function.comp_def,physicalScalarTruncate,LinearIsometryEquiv.symm_apply_apply] using! hl

/-- Actual scalar Fourier approximants have uniformly convergent trajectories. -/
theorem tendstoUniformly_fourthScalarTruncate (hp : p ≠ ⊤) (hp1 : 1 < p) (T : ℝ)
    (u : PhysicalScalarRealInput p) (hu : u ∈ fourthScalarTrajectoryDomain hp hp1 T) :
    TendstoUniformly (fun N (time : Icc (-T) T) => fourthScalarImageFlow hp hp1 (physicalScalarTruncate N u) time.val)
      (fun time => fourthScalarImageFlow hp hp1 u time.val) atTop :=
  tendstoUniformly_fourthScalarImageFlow hp hp1 T _ u hu (tendsto_physicalScalarTruncate hp u)

/-- Any family of actual scalar lift trajectories converging pointwise has
exactly the same limit as the fixed lift. In particular no choice of
approximants can change its limit. This does not assume PDE agreement. -/
theorem fourthScalarImageFlow_limit_unique (hp : p ≠ ⊤) (hp1 : 1 < p) (T : ℝ)
    {ι : Type*} {l : Filter ι} [NeBot l] (u : ι → PhysicalScalarRealInput p) (v : PhysicalScalarRealInput p)
    (hv : v ∈ fourthScalarTrajectoryDomain hp hp1 T) (hu : Tendsto u l (𝓝 v))
    (q : Icc (-T) T → PhysicalScalarRealInput p)
    (hq : ∀ time, Tendsto (fun i => fourthScalarImageFlow hp hp1 (u i) time.val) l (𝓝 (q time))) :
    q = fun time => fourthScalarImageFlow hp hp1 v time.val := by
  funext time
  exact tendsto_nhds_unique (hq time)
    ((tendstoUniformly_fourthScalarImageFlow hp hp1 T u v hv hu).tendsto_at time)

end NLS.Articles.MKdVBelowL2
