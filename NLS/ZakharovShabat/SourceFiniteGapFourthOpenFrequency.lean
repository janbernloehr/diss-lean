import NLS.ZakharovShabat.SourceFullAbelianFourthContourLocal
import NLS.ZakharovShabat.SourceAbelianMomentFourthContour
import NLS.ZakharovShabat.SourceFiniteGapMomentumNormalization

/-! # The physical H₄ frequency at an open finite-gap action

The frequency is defined as the negative derivative of the physical fourth
Hamiltonian along the actual Birkhoff action-reduction curve. A fixed quartic
contour computes this derivative and gives the exact renormalized moment sum.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology Complex NLS.Poisson
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W V₀ C V X U Wa : Set (CoeffPair 2)}
  {s u : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The open-action H₄ frequency is independently defined by its physical derivative. -/
def finiteGapFourthOpenFrequency
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (_hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0) : ℂ :=
  -deriv (D.physicalActionReductionHamiltonian φ hf n 4) 0

/-- Differentiate actual physical H₄, including both product-renormalization terms. -/
theorem hasDerivAt_physicalActionReductionHamiltonian_four
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (F : SourceFullAbelianDifferentialData (by simp) (by norm_num) X U)
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0)
    (R : ℝ) (hR : 0 < R)
    (hcircle : sphere (0:ℂ) R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) φ.val)
    (hseg : ∀ k ∈ hf.toFinset, sourcePeriodicSegment (by simp) (by norm_num) φ.val k ⊆ ball 0 R) :
    HasDerivAt (D.physicalActionReductionHamiltonian φ hf n 4)
      (-sourceAngularThetaFunctionalBracket (by simp) (by norm_num) le_rfl n u
        (sourceFullAbelianFourthContour (by simp) (by norm_num) X 0 R) φ.val-
        6*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 2-
        (12*Real.pi:ℂ)*n*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1) 0 := by
  have ha := hilbert_action_pos_of_gap_ne_zero φ n hn
  let γ := fun t : ℝ => (D.hilbertActionReduction φ n t).val
  let H := sourceFullAbelianFourthContour (by simp) (by norm_num) X 0 R
  let M₁ := sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1
  let M₂ := sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 2
  let b := sourceAngularThetaFunctionalBracket (by simp) (by norm_num) le_rfl n u H φ.val
  have hγ : HasDerivAt γ
      (sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n u φ.val) 0 := by
    simpa only [γ,D.hilbertActionReduction_zero] using
      D.hasDerivAt_hilbertActionReduction_thetaHamiltonian E n φ ha ha
  have hγlim : Tendsto γ (𝓝 0) (𝓝 φ.val) := by
    simpa only [γ,D.hilbertActionReduction_zero] using hγ.continuousAt.tendsto
  have hH := F.analyticAt_fourthContour 0 R hR.le φ.val (F.real_subset φ.property) hcircle
  have hc : HasDerivAt (fun t => H (γ t)) (-b) 0 := by
    have hHγ : HasFDerivAt H (fderiv ℂ H φ.val) (γ 0) := by
      simpa only [γ,D.hilbertActionReduction_zero] using hH.differentiableAt.hasFDerivAt
    have hh := (hHγ.restrictScalars ℝ).comp_hasDerivAt 0 hγ
    change HasDerivAt (fun t => H (γ t))
      ((fderiv ℂ H φ.val) (sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n u φ.val)) 0 at hh
    rw [sourceAngularThetaHamiltonianVector,apply_sourceHamiltonianDirection,sourceBivector_antisymm] at hh
    exact hh
  have ht : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 0 := by
    simpa using! (Complex.ofRealCLM.hasDerivAt (x := (0:ℝ)))
  have hm₁ : HasDerivAt (D.physicalActionReductionHamiltonian φ hf n 1) (-1) 0 := by
    have hd : HasDerivAt (fun t : ℝ => M₁-(t:ℂ)) (-1) 0 := by
      simpa using! (hasDerivAt_const (0:ℝ) M₁).sub ht
    apply hd.congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds ha] with t ht
    exact D.hilbertActionReduction_physical_mass φ hf n hn ha t ht.le
  have hm₂ : HasDerivAt (D.physicalActionReductionHamiltonian φ hf n 2) (-(2*(Real.pi:ℂ)*n)) 0 := by
    have hd := D.hasDerivAt_physicalActionReductionHamiltonian_two E φ hf n hn 0 ha
    simpa only [D.hilbertActionReduction_zero,D.finiteGap_momentum_bracket_normalized E F A φ hf n hn] using hd
  have hp := (hm₁.mul hm₂).const_mul (6:ℂ)
  have hprod : HasDerivAt (fun t => 6*D.physicalActionReductionHamiltonian φ hf n 1 t*
      D.physicalActionReductionHamiltonian φ hf n 2 t) (-6*M₂-(12*Real.pi:ℂ)*n*M₁) 0 := by
    convert! hp using 1
    · funext t
      simp only [Pi.mul_apply]
      ring
    · simp only [physicalActionReductionHamiltonian,D.hilbertActionReduction_zero]
      dsimp [M₁,M₂]
      ring
  have hder : HasDerivAt (fun t => H (γ t)+6*D.physicalActionReductionHamiltonian φ hf n 1 t*
      D.physicalActionReductionHamiltonian φ hf n 2 t) (-b-6*M₂-(12*Real.pi:ℂ)*n*M₁) 0 := by
    convert! hc.add hprod using 1
    ring
  apply hder.congr_of_eventuallyEq
  have heq := hγlim.eventually (F.eventually_fourthContour_eq_physical_of_gap_support φ hf.toFinset R hR hseg)
  filter_upwards [heq] with t heq
  have hval := heq (D.hilbertActionReduction φ n t).property
    (D.hilbertActionReduction_mem_finiteGap φ hf n t) (D.hilbertActionReduction_gap_support φ hf n hn t)
  change H (γ t) = D.physicalActionReductionHamiltonian φ hf n 4 t-
    6*D.physicalActionReductionHamiltonian φ hf n 1 t*D.physicalActionReductionHamiltonian φ hf n 2 t at hval
  linear_combination -hval

/-- The physical open frequency is the quartic bracket with the exact H₁,H₂ corrections. -/
theorem finiteGapFourthOpenFrequency_eq_fourthContour_bracket
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (F : SourceFullAbelianDifferentialData (by simp) (by norm_num) X U)
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0)
    (R : ℝ) (hR : 0 < R)
    (hcircle : sphere (0:ℂ) R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) φ.val)
    (hseg : ∀ k ∈ hf.toFinset, sourcePeriodicSegment (by simp) (by norm_num) φ.val k ⊆ ball 0 R) :
    D.finiteGapFourthOpenFrequency φ hf n hn =
      sourceAngularThetaFunctionalBracket (by simp) (by norm_num) le_rfl n u
        (sourceFullAbelianFourthContour (by simp) (by norm_num) X 0 R) φ.val+
        6*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 2+
        (12*Real.pi:ℂ)*n*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1 := by
  rw [finiteGapFourthOpenFrequency,
    (D.hasDerivAt_physicalActionReductionHamiltonian_four E F A φ hf n hn R hR hcircle hseg).deriv]
  ring

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
