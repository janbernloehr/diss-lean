import NLS.ZakharovShabat.SourceFullAbelianMomentumPoisson
import NLS.ZakharovShabat.SourceFiniteGapAngleMomentum

/-! # Physical angle–momentum normalization at real finite-gap sources

A fixed contour agrees with physical H₂ along the actual action-reduction
curve. Differentiating that equality identifies the physical bracket,
independently defined through the H¹ momentum cotangent, with 2πn.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
open NLS.Poisson
variable {W₀ B W V₀ C V X U Wa : Set (CoeffPair 2)}
  {s u : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Along the actual action-reduction curve, the H₂ derivative is minus the fixed-contour bracket. -/
theorem hasDerivAt_physicalActionReductionHamiltonian_two_contour
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (F : SourceFullAbelianDifferentialData (by simp) (by norm_num) X U)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0)
    (R : ℝ) (hR : 0 < R)
    (hcircle : sphere (0 : ℂ) R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) φ.val)
    (hseg : ∀ k ∈ hf.toFinset, sourcePeriodicSegment (by simp) (by norm_num) φ.val k ⊆ ball 0 R) :
    HasDerivAt (D.physicalActionReductionHamiltonian φ hf n 2)
      (-sourceAngularThetaFunctionalBracket (by simp) (by norm_num) le_rfl n u
        (sourceFullAbelianMomentumContour (by simp) (by norm_num) X 0 R) φ.val) 0 := by
  have ha := hilbert_action_pos_of_gap_ne_zero φ n hn
  let γ := fun t : ℝ => (D.hilbertActionReduction φ n t).val
  let H := sourceFullAbelianMomentumContour (by simp) (by norm_num) X 0 R
  let b := sourceAngularThetaFunctionalBracket (by simp) (by norm_num) le_rfl n u H φ.val
  have hγ : HasDerivAt γ
      (sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n u φ.val) 0 := by
    simpa only [γ,D.hilbertActionReduction_zero] using
      D.hasDerivAt_hilbertActionReduction_thetaHamiltonian E n φ ha ha
  have hγlim : Tendsto γ (𝓝 0) (𝓝 φ.val) := by
    simpa only [γ,D.hilbertActionReduction_zero] using hγ.continuousAt.tendsto
  have hH := F.analyticAt_momentumContour 0 R hR.le φ.val (F.real_subset φ.property) hcircle
  have hc : HasDerivAt (fun t => H (γ t)) (-b) 0 := by
    have hHγ : HasFDerivAt H (fderiv ℂ H φ.val) (γ 0) := by
      simpa only [γ,D.hilbertActionReduction_zero] using hH.differentiableAt.hasFDerivAt
    have hh := (hHγ.restrictScalars ℝ).comp_hasDerivAt 0 hγ
    change HasDerivAt (fun t => H (γ t))
      ((fderiv ℂ H φ.val) (sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n u φ.val)) 0 at hh
    rw [sourceAngularThetaHamiltonianVector,apply_sourceHamiltonianDirection,sourceBivector_antisymm] at hh
    exact hh
  apply hc.congr_of_eventuallyEq
  have heq := hγlim.eventually
    (F.eventually_momentumContour_eq_physical_of_gap_support φ hf.toFinset R hR hseg)
  filter_upwards [heq] with t heq
  exact (heq (D.hilbertActionReduction φ n t).property
    (D.hilbertActionReduction_mem_finiteGap φ hf n t)
    (D.hilbertActionReduction_gap_support φ hf n hn t)).symm

/-- The independently defined H¹ momentum bracket equals 2πn at every real finite-gap source. -/
theorem finiteGap_momentum_bracket_normalized
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (F : SourceFullAbelianDifferentialData (by simp) (by norm_num) X U)
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0) :
    sourceSobolevThetaMomentumBracket n u (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf) =
      2*(Real.pi : ℂ)*n := by
  obtain ⟨T,_,hbr⟩ := E.exists_finiteGap_momentumContour_bracket F A le_rfl φ hf
  obtain ⟨R,hR,hTR,hcircle,hseg⟩ :=
    exists_sourceCanonicalRoot_circle_enclosing_finite_gaps (by simp) (by norm_num) φ.val hf.toFinset T
  have hd := D.hasDerivAt_physicalActionReductionHamiltonian_two_contour E F φ hf n hn R hR hcircle hseg
  rw [D.finiteGap_momentum_bracket_eq_physical_deriv E φ hf n hn,hd.deriv,neg_neg]
  exact hbr R hTR hcircle n hn
end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
