import NLS.ZakharovShabat.SourceHilbertActionReductionFiniteGap
import NLS.ZakharovShabat.SourceFullAbelianPhysicalContourLocal
import NLS.ZakharovShabat.SourceAbelianMomentFiniteGapContour

/-! # Physical finite-gap frequencies at open actions

The physical third Hamiltonian is differentiated along the actual Birkhoff
action-reduction curve. Local equality with one fixed cubic contour justifies
the derivative. The negative action derivative, rather than a moment formula,
defines the open-action frequency. Closed selected actions require a separate
continuity argument.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.Poisson
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W V₀ C V X U : Set (CoeffPair 2)}
  {s u : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Evaluate the physical hierarchy along the actual action-reduction curve. -/
def physicalActionReductionHamiltonian
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (j : ℕ) (t : ℝ) : ℂ :=
  sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (D.hilbertActionReduction φ n t)
    (D.hilbertActionReduction_mem_finiteGap φ hf n t) j

/-- The negative derivative of the physical `H3` when only the selected
action is decreased at unit speed. This definition is restricted to open actions. -/
def finiteGapOpenFrequency
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (_hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0) : ℂ :=
  -deriv (D.physicalActionReductionHamiltonian φ hf n 3) 0

/-- A fixed contour represents the physical Hamiltonian on a neighborhood
of time zero, so its actual angle bracket computes the physical derivative. -/
theorem hasDerivAt_physicalActionReductionHamiltonian_three
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (F : SourceFullAbelianDifferentialData (by simp) (by norm_num) X U)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0)
    (R : ℝ) (hR : 0 < R)
    (hcircle : sphere (0 : ℂ) R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) φ.val)
    (hseg : ∀ k ∈ hf.toFinset, sourcePeriodicSegment (by simp) (by norm_num) φ.val k ⊆ ball 0 R) :
    HasDerivAt (D.physicalActionReductionHamiltonian φ hf n 3)
      (-sourceAngularThetaFunctionalBracket (by simp) (by norm_num) le_rfl n u
        (sourceFullAbelianCubicContour (by simp) (by norm_num) X 0 R) φ.val -
          4*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1) 0 := by
  have haction := sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num) φ.val φ.property n
  have ha : 0 < (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re := by
    apply lt_of_le_of_ne haction.1
    intro he
    have hz := haction.2.2.mp (Complex.ext he.symm haction.2.1)
    exact hn (by simpa only [sourcePeriodicGapDisplacement_apply] using hz)
  let γ := fun t : ℝ => (D.hilbertActionReduction φ n t).val
  let H := sourceFullAbelianCubicContour (by simp) (by norm_num) X 0 R
  let M := sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1
  let b := sourceAngularThetaFunctionalBracket (by simp) (by norm_num) le_rfl n u H φ.val
  have hγ : HasDerivAt γ
      (sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n u φ.val) 0 := by
    simpa only [γ,D.hilbertActionReduction_zero] using
      D.hasDerivAt_hilbertActionReduction_thetaHamiltonian E n φ ha ha
  have hγlim : Tendsto γ (𝓝 0) (𝓝 φ.val) := by
    simpa only [γ,D.hilbertActionReduction_zero] using hγ.continuousAt.tendsto
  have hH := F.analyticAt_cubicContour 0 R hR.le φ.val (F.real_subset φ.property) hcircle
  have hc : HasDerivAt (fun t => H (γ t)) (-b) 0 := by
    have hHγ : HasFDerivAt H (fderiv ℂ H φ.val) (γ 0) := by
      simpa only [γ,D.hilbertActionReduction_zero] using hH.differentiableAt.hasFDerivAt
    have hh := (hHγ.restrictScalars ℝ).comp_hasDerivAt 0 hγ
    change HasDerivAt (fun t => H (γ t))
      ((fderiv ℂ H φ.val) (sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n u φ.val)) 0 at hh
    rw [sourceAngularThetaHamiltonianVector,apply_sourceHamiltonianDirection,sourceBivector_antisymm] at hh
    exact hh
  have ht : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    simpa using! (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ)))
  have hm := (((hasDerivAt_const (0 : ℝ) M).sub ht).pow 2).const_mul (2 : ℂ)
  have hder : HasDerivAt (fun t => H (γ t)+2*(M-(t : ℂ))^2) (-b-4*M) 0 := by
    convert! hc.add hm using 1
    norm_num
    ring
  apply hder.congr_of_eventuallyEq
  have heq := hγlim.eventually
    (F.eventually_cubicContour_eq_physical_of_gap_support φ hf.toFinset R hR hseg)
  filter_upwards [heq,gt_mem_nhds ha] with t heq ht
  have hval := heq (D.hilbertActionReduction φ n t).property
    (D.hilbertActionReduction_mem_finiteGap φ hf n t) (D.hilbertActionReduction_gap_support φ hf n hn t)
  have hmass := D.hilbertActionReduction_physical_mass φ hf n hn ha t ht.le
  change H (γ t) = D.physicalActionReductionHamiltonian φ hf n 3 t-
    2*(D.physicalActionReductionHamiltonian φ hf n 1 t)^2 at hval
  change D.physicalActionReductionHamiltonian φ hf n 1 t = M-(t : ℂ) at hmass
  rw [hmass] at hval
  linear_combination -hval

/-- The open-action physical frequency is the contour bracket plus the
mass correction; this is now a derivative identity, not just equality of values. -/
theorem finiteGapOpenFrequency_eq_cubicContour_bracket
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (F : SourceFullAbelianDifferentialData (by simp) (by norm_num) X U)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0)
    (R : ℝ) (hR : 0 < R)
    (hcircle : sphere (0 : ℂ) R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) φ.val)
    (hseg : ∀ k ∈ hf.toFinset, sourcePeriodicSegment (by simp) (by norm_num) φ.val k ⊆ ball 0 R) :
    D.finiteGapOpenFrequency φ hf n hn =
      sourceAngularThetaFunctionalBracket (by simp) (by norm_num) le_rfl n u
        (sourceFullAbelianCubicContour (by simp) (by norm_num) X 0 R) φ.val +
          4*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1 := by
  rw [finiteGapOpenFrequency,
    (D.hasDerivAt_physicalActionReductionHamiltonian_three E F φ hf n hn R hR hcircle hseg).deriv]
  ring

/-- Lemma 20.2 for a real finite-gap Hilbert source with an open selected
action, using the physical Hamiltonian's action derivative. -/
theorem finiteGapOpenFrequency_renormalized_eq_moments_of_data
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (F : SourceFullAbelianDifferentialData (by simp) (by norm_num) X U)
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) X u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0) :
    D.finiteGapOpenFrequency φ hf n hn -
      4*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1 - (2*(n : ℂ)*Real.pi)^2 =
        -(4/(2*Real.pi) : ℂ)*(∑' k : ℤ, A.moment n k 2 φ.val) := by
  obtain ⟨T,_,hformula⟩ := E.exists_finiteGap_cubicContour_moment_formula F A le_rfl φ hf
  obtain ⟨R,hR,hTR,hcircle,hseg⟩ := exists_sourceCanonicalRoot_circle_enclosing_finite_gaps
    (by simp) (by norm_num) φ.val hf.toFinset T
  rw [D.finiteGapOpenFrequency_eq_cubicContour_bracket E F φ hf n hn R hR hcircle hseg,
    add_sub_cancel_right]
  exact hformula R hTR hcircle n hn

/-- The physical frequency formula for any normalized moment atlas.
The angle and primitive differential data are constructed internally;
their domains and normalized branches need not match the atlas. -/
theorem finiteGapOpenFrequency_renormalized_eq_moments
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) X u)
    (hs : SourcePsiNormalizedComplexExtension (by simp) (by norm_num) V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0) :
    D.finiteGapOpenFrequency φ hf n hn -
      4*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1 - (2*(n : ℂ)*Real.pi)^2 =
        -(4/(2*Real.pi) : ℂ)*(∑' k : ℤ, A.moment n k 2 φ.val) := by
  obtain ⟨Y,Z,_,F⟩ := exists_sourceFullAbelianDifferentialData (p := 2) (by simp) (by norm_num)
  obtain ⟨V₁,B₁,V₂,_,_,_,_,_,_,v,E⟩ := exists_sourceAngularTheta_theorem13_1_iv (p := 2) (by simp) (by norm_num)
  obtain ⟨T,_,hformula⟩ := A.exists_finiteGap_quadratic_contour_formula hs φ hf
  obtain ⟨R,hR,hTR,hcircle,hseg⟩ := exists_sourceCanonicalRoot_circle_enclosing_finite_gaps
    (by simp) (by norm_num) φ.val hf.toFinset T
  obtain ⟨Fφ⟩ := F.charts φ.val (F.real_subset φ.property)
  obtain ⟨Aφ⟩ := (A.localChart φ).charts φ.val (mem_ball_self (A.localChart φ).radius_pos)
  have hbranch : (v n φ.val : Coeff 2) = (u n φ.val : Coeff 2) := by
    rw [E.psi.real_agreement n φ,hs.real_agreement n φ]
  rw [D.finiteGapOpenFrequency_eq_cubicContour_bracket E F φ hf n hn R hR hcircle hseg,
    add_sub_cancel_right,E.theta_cubicContour_eq_quadratic F le_rfl n φ (F.real_subset φ.property) hn 0 R hR.le hcircle,
    hbranch,sourceAbelianMomentCircle_independent_neighborhood (by simp) (by norm_num) Y X n 0 2
      (u n φ.val) φ.val Fφ Aφ 0 R hR.le hcircle]
  exact hformula R hTR hcircle n hn

/-- The physical action derivative is independent of the chosen compatible
Birkhoff data, even when the source neighborhoods and psi branches differ. -/
theorem finiteGapOpenFrequency_independent_coordinates
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (D' : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₀ C V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0) :
    D.finiteGapOpenFrequency φ hf n hn = D'.finiteGapOpenFrequency φ hf n hn := by
  classical
  obtain ⟨Y,Z,_,_,_,_,v,hs,hlocal⟩ := exists_sourceAbelianMoment_localCharts (p := 2) (by simp) (by norm_num)
  choose L hL using hlocal
  let A : SourceAbelianMomentAtlas (by simp) (by norm_num) Y v := ⟨L⟩
  have hD := D.finiteGapOpenFrequency_renormalized_eq_moments A hs φ hf n hn
  have hD' := D'.finiteGapOpenFrequency_renormalized_eq_moments A hs φ hf n hn
  linear_combination hD-hD'

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
