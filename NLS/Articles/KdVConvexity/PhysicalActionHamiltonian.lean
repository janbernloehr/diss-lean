import NLS.Articles.KdVConvexity.OriginalActionDomainRealization
import NLS.Articles.KdVConvexity.ActualH1HamiltonianExtension
import NLS.Articles.KdVConvexity.OriginalWeightedActionSpace

/-! # The physical action Hamiltonian and its analytic renormalized extension -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVConvexity
open NLS.KdV

/-- An actual mean-zero physical H1 representative of every point of the
entire original positive ell^(3,1) action domain. -/
def originalActionSource (a : originalPositiveActionDomain) : RealHillWeightedPotential hillH1SpectralWeight :=
  Classical.choose (exists_H1_source_of_original_positive_actions a.val a.property)

theorem originalActionSource_mean_zero (a : originalPositiveActionDomain) :
    (originalActionSource a).val.val 0=0 :=
  (Classical.choose_spec (exists_H1_source_of_original_positive_actions a.val a.property)).1

theorem originalActionSource_actions (a : originalPositiveActionDomain) :
    physicalHilbertActions hillH1SpectralWeight (originalActionSource a)=a.val :=
  (Classical.choose_spec (exists_H1_source_of_original_positive_actions a.val a.property)).2

/-- Physical KdV energy as a function of its original actions. Agreement
with every physical H1 representative is proved below, so this value does
not depend on the representative selected here. -/
def physicalActionHamiltonian (a : originalPositiveActionDomain) : ℂ :=
  hillNativeH1Hamiltonian (originalActionSource a).val

/-- The physical renormalization in Theorem 1.1, with its original
linear frequencies 8*pi^3*n^3 and positive-index raw actions. -/
def physicalRenormalizedActionHamiltonian (a : originalPositiveActionDomain) : ℂ :=
  physicalActionHamiltonian a-∑' n : ℕ+, ((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*a.val n

theorem physicalActionHamiltonian_eq_source
    (a : originalPositiveActionDomain) (q : RealHillWeightedPotential hillH1SpectralWeight)
    (hm : q.val.val 0=0) (ha : physicalHilbertActions hillH1SpectralWeight q=a.val) :
    physicalActionHamiltonian a=hillNativeH1Hamiltonian q.val := by
  obtain ⟨_V,R,_hV,_hpos,_hH,hphys⟩ := exists_actual_analytic_Hamiltonian_extension_with_H1_physical_identity
  have hq := hphys q hm
  have hc := hphys (originalActionSource a) (originalActionSource_mean_zero a)
  rw [ha] at hq
  rw [originalActionSource_actions] at hc
  have hlinear : hillH1LinearActionEnergy q=hillH1LinearActionEnergy (originalActionSource a) := by
    rw [hillH1LinearActionEnergy_eq_physicalHilbertActions,
      hillH1LinearActionEnergy_eq_physicalHilbertActions,ha,originalActionSource_actions]
  have he := hq.symm.trans hc
  rw [hlinear] at he
  change hillNativeH1Hamiltonian (originalActionSource a).val=hillNativeH1Hamiltonian q.val
  linear_combination -he

/-- The independently defined action energy agrees with the literal
physical H1 integral at every mean-zero source, with no phase restriction. -/
theorem physicalRenormalizedActionHamiltonian_eq_source
    (q : RealHillWeightedPotential hillH1SpectralWeight) (hm : q.val.val 0=0) :
    physicalRenormalizedActionHamiltonian
      ⟨physicalHilbertActions hillH1SpectralWeight q,physicalHilbertActions_H1_mem_original_domain q⟩ =
      classicalHamiltonian (fun x : ℝ => hillNativeH1Continuous q.val (x : AddCircle (2 : ℝ)))-
        hillH1LinearActionEnergy q := by
  rw [physicalRenormalizedActionHamiltonian,physicalActionHamiltonian_eq_source _ q hm rfl,
    ←hillH1LinearActionEnergy_eq_physicalHilbertActions,hillNativeH1Hamiltonian_eq_physical_integral]

/-- The global physical analytic-extension assertion of Theorem 1.1:
one complex open neighborhood of the ENTIRE positive ell2 quadrant carries
the actual contour Hamiltonian and agrees with physical Hstar on the
ENTIRE original positive ell^(3,1) action domain, including its boundary.
The physical frequency and Taylor assertions remain separate work. -/
theorem exists_global_analytic_physical_Hstar_extension :
    ∃ V : Set ActionSpace, ∃ R : ℕ+ → BaseActionSpace → ℂ,
      IsOpen V ∧ positiveQuadrant ⊆ V ∧ AnalyticOnNhd ℂ (contourHamiltonian R) V ∧
      ∀ a : originalPositiveActionDomain, contourHamiltonian R a.val=physicalRenormalizedActionHamiltonian a := by
  obtain ⟨V,R,hV,hpos,hH,hphys⟩ := exists_actual_analytic_Hamiltonian_extension_with_H1_physical_identity
  refine ⟨V,R,hV,hpos,hH,?_⟩
  intro a
  have hc := hphys (originalActionSource a) (originalActionSource_mean_zero a)
  rw [originalActionSource_actions,hillH1LinearActionEnergy_eq_physicalHilbertActions,
    originalActionSource_actions] at hc
  exact hc

/-- The original physical Hstar on the positive cone of the actual
weighted ell^(3,1) Banach space, before its continuous ell2 inclusion. -/
def originalPhysicalHstar (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1) : ℂ :=
  physicalRenormalizedActionHamiltonian
    ⟨originalActionInclusion b.val,originalActionInclusion_mem_domain b.val b.property⟩

theorem originalPhysicalHstar_eq_source
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1)
    (q : RealHillWeightedPotential hillH1SpectralWeight) (hm : q.val.val 0=0)
    (ha : physicalHilbertActions hillH1SpectralWeight q=originalActionInclusion b.val) :
    originalPhysicalHstar b =
      classicalHamiltonian (fun x : ℝ => hillNativeH1Continuous q.val (x : AddCircle (2 : ℝ)))-
        ∑' n : ℕ+, ((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*(originalActionInclusion b.val) n := by
  rw [originalPhysicalHstar,physicalRenormalizedActionHamiltonian,
    physicalActionHamiltonian_eq_source _ q hm ha,hillNativeH1Hamiltonian_eq_physical_integral]

/-- The physical global analytic-extension component of Theorem 1.1,
stated on the original weighted action Banach space and its actual
coefficient-preserving continuous inclusion into positive-index ell2. -/
theorem exists_global_analytic_extension_of_original_physical_Hstar :
    ∃ V : Set ActionSpace, ∃ H : ActionSpace → ℂ,
      IsOpen V ∧ positiveQuadrant ⊆ V ∧ AnalyticOnNhd ℂ H V ∧
      ∀ b : WeightedCoeff.nonnegativeLocus originalActionWeight 1,
        H (originalActionInclusion b.val)=originalPhysicalHstar b := by
  obtain ⟨V,R,hV,hpos,hH,hphysical⟩ := exists_global_analytic_physical_Hstar_extension
  refine ⟨V,contourHamiltonian R,hV,hpos,hH,?_⟩
  intro b
  exact hphysical ⟨originalActionInclusion b.val,originalActionInclusion_mem_domain b.val b.property⟩

end NLS.Articles.KdVConvexity
