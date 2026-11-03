import NLS.Articles.KdVPseudomeasures.OriginalComplexDirichletMultiplicity
import NLS.KdV.HminusOneDirichletCentralBounds
import NLS.KdV.HminusOneDirichletCentralRoots

/-! Full ORIGINAL complex distribution central Dirichlet spectra.
Counts use actual native algebraic root spaces, including central associated
vectors. Neighborhoods carry the original H^-1 norm topology. -/
noncomputable section
open Set
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat

instance originalComplexHminusOnePotentialTopology : TopologicalSpace OriginalComplexHminusOnePotential :=
  TopologicalSpace.induced (fun q : OriginalComplexHminusOnePotential => q.val) inferInstance

/-- Actual original native central spectrum in one fixed local Miura chart. -/
def originalComplexDirichletCentralSpectrum (C : HillHminusMiuraChart)
    (q : OriginalComplexHminusOnePotential) (N : ℕ) : Finset ℂ :=
  hillHminusDirichletCentralSpectrum (periodOneOriginalExtract q.val)
    (C.lift (periodOneOriginalExtract q.val)) C.energyShift N

/-- This is exactly the ENTIRE original operator spectrum in the specified
central region, with no change to the original smooth-test distribution. -/
theorem mem_originalComplexDirichletCentralSpectrum (C : HillHminusMiuraChart)
    (q : OriginalComplexHminusOnePotential)
    (hq : periodOneOriginalExtract q.val ∈ C.domain) (N : ℕ) (e : ℂ) :
    e ∈ originalComplexDirichletCentralSpectrum C q N ↔
      e ∈ singularDirichletSpectrum q.val ∧
        e ∈ (fun z : ℂ => z^2-C.energyShift) '' centralSpectralBox N := by
  have h := mem_hillHminusDirichletCentralSpectrum (periodOneOriginalExtract q.val)
    (C.lift (periodOneOriginalExtract q.val)) C.energyShift (C.image _ hq) N e
  rw [originalComplexDirichlet_distribution q] at h
  exact h

/-- All actual original central eigenvalues have the same explicit bound. -/
theorem norm_le_of_mem_originalComplexDirichletCentralSpectrum (C : HillHminusMiuraChart)
    (q : OriginalComplexHminusOnePotential)
    (hq : periodOneOriginalExtract q.val ∈ C.domain) (N : ℕ) (e : ℂ)
    (he : e ∈ originalComplexDirichletCentralSpectrum C q N) :
    ‖e‖ ≤ ((N:ℝ)*Real.pi+Real.pi/2+N)^2+‖C.energyShift‖ :=
  norm_le_of_mem_hillHminusDirichletCentralSpectrum (periodOneOriginalExtract q.val)
    (C.lift (periodOneOriginalExtract q.val)) C.energyShift (C.image _ hq) N e he

/-- ONE original H^-1 norm neighborhood and ONE fixed chart/cutoff give,
for EVERY larger cutoff, precisely N ACTUAL native algebraic repetitions
and a uniform bound on every central energy, for ALL complex original
physically period-one distributions in the neighborhood. -/
theorem exists_uniform_originalComplexDirichletCentralCount
    (q : OriginalComplexHminusOnePotential) :
    ∃ C : HillHminusMiuraChart, ∃ N₀ : ℕ, ∃ U : Set OriginalComplexHminusOnePotential,
      0 < N₀ ∧ IsOpen U ∧ q ∈ U ∧
      (∀ a ∈ U, periodOneOriginalExtract a.val ∈ C.domain) ∧
      ∀ a ∈ U, ∀ N : ℕ, N₀ ≤ N →
        (∑ e ∈ originalComplexDirichletCentralSpectrum C a N,
          singularDirichletAlgebraicMultiplicity a.val e) = N ∧
        ∀ e ∈ originalComplexDirichletCentralSpectrum C a N,
          ‖e‖ ≤ ((N:ℝ)*Real.pi+Real.pi/2+N)^2+‖C.energyShift‖ := by
  let F : OriginalComplexHminusOnePotential → PeriodOneHminusOne :=
    fun a => periodOneOriginalExtract a.val
  have hF : Continuous F := periodOneOriginalExtract.continuous.comp continuous_subtype_val
  let C := hillHminusMiuraChartAt (F q)
  obtain ⟨N₀,V,hN,hV,hqV,hsub,hcount⟩ :=
    C.exists_uniform_dirichletCentralCount (F q) (mem_hillHminusMiuraChartAt _)
  refine ⟨C,N₀,F ⁻¹' V,hN,hV.preimage hF,hqV,fun a ha => hsub ha,?_⟩
  intro a ha N hNa
  have hc := hcount (F a) ha N hNa
  change (∑ e ∈ originalComplexDirichletCentralSpectrum C a N,
    singularDirichletAlgebraicMultiplicity (periodOneOriginal (periodOneOriginalExtract a.val)) e) = N at hc
  rw [originalComplexDirichlet_distribution a] at hc
  exact ⟨hc,fun e he => norm_le_of_mem_originalComplexDirichletCentralSpectrum
    C a (hsub ha) N e he⟩

end NLS.Articles.KdVPseudomeasures
