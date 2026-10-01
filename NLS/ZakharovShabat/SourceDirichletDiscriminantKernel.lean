import NLS.ZakharovShabat.SourceBoundaryTerminalPoisson
import NLS.ZakharovShabat.SourceIsospectralDirection
import NLS.ComplexAnalysis.SimplePoleQuotient

/-! # The actual Dirichlet discriminant kernel at every parameter

A divided difference fills the apparent pole at the Dirichlet root.
The actual root and full moving terminal anti-discriminant have this
same kernel, including coincident parameters and branch terminals.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The entire discriminant kernel uses the actual simple Dirichlet
derivative and its analytic divided difference. -/
def sourceDirichletDiscriminantKernel (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (φ : CoeffPair p) (w : ℂ) : ℂ :=
  let χ := periodOneBoundaryCharacteristic hp hp1 .dirichlet φ;
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n;
  -(2*deriv χ μ)⁻¹*dslope χ μ w

theorem sourceDirichletDiscriminantKernel_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : CoeffPair p) (w : ℂ)
    (hw : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n ≠ w) :
    sourceDirichletDiscriminantKernel hp hp1 n φ w =
      periodOneBoundaryCharacteristic hp hp1 .dirichlet φ w/
        (2*(canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n-w)*
          deriv (periodOneBoundaryCharacteristic hp hp1 .dirichlet φ)
            (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n)) := by
  dsimp only [sourceDirichletDiscriminantKernel]
  rw [dslope_of_ne _ hw.symm]
  simp only [slope,vsub_eq_sub,periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero,
    sub_zero,smul_eq_mul,div_eq_mul_inv,mul_inv_rev]
  rw [show canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n-w =
    -(w-canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n) by ring,inv_neg]
  ring

theorem sourceDirichletDiscriminantKernel_at_root
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) :
    sourceDirichletDiscriminantKernel hp hp1 n φ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n) = -(1/2 : ℂ) := by
  dsimp only [sourceDirichletDiscriminantKernel]
  rw [dslope_same]
  have hd := deriv_periodOneBoundaryCharacteristic_at_canonicalRoot_ne_zero_of_realType
    hp hp1 .dirichlet φ hreal n
  field_simp [hd]

theorem analyticOnNhd_sourceDirichletDiscriminantKernel
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : CoeffPair p) :
    AnalyticOnNhd ℂ (sourceDirichletDiscriminantKernel hp hp1 n φ) univ := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n
  let χ := periodOneBoundaryCharacteristic hp hp1 .dirichlet φ
  intro w _
  have hχ : AnalyticAt ℂ χ w :=
    analyticOnNhd_periodOneBoundaryCharacteristic hp hp1 .dirichlet φ w (mem_univ _)
  have hs : AnalyticAt ℂ (dslope χ μ) w := by
    by_cases hw : w = μ
    · subst w; exact analyticAt_dslope_same hχ
    · have he : dslope χ μ =ᶠ[𝓝 w] (fun z => (χ z-χ μ)/(z-μ)) := by
        filter_upwards [isOpen_ne.mem_nhds hw] with z hz
        simp only [dslope_of_ne χ hz,slope,vsub_eq_sub,smul_eq_mul]
        ring
      exact ((hχ.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr hw)).congr he.symm
  exact analyticAt_const.mul hs

/-- Every fixed-parameter discriminant Hamiltonian direction is
actually isospectral at every complex source. -/
theorem sourceHamiltonianVector_discriminant_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair p) (w : ℂ) :
    SourceIsospectralDirection hp φ (sourceHamiltonianVector h2p
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ) := by
  intro z
  rw [sourceDiscriminantCotangent,fderiv_apply_sourceHamiltonianVector]
  exact sourceBracket_discriminants_eq_zero hp hp1 h2p φ z w

/-- The actual moving Dirichlet coordinate has the filled kernel,
including at its own spectral parameter and at periodic terminals. -/
theorem sourceBracket_dirichletRoot_discriminant_eq_kernel
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (n : ℤ) (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) (w : ℂ) :
    sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ =
      sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet n φ*
        sourceDirichletDiscriminantKernel hp hp1 n φ w := by
  change sourceBoundaryRootDiscriminantBracket hp hp1 h2p .dirichlet φ n w = _
  by_cases hw : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n = w
  · rw [← hw,sourceBoundaryRootDiscriminantBracket_at_root hp hp1 h2p .dirichlet φ hreal n,
      sourceDirichletDiscriminantKernel_at_root hp hp1 n φ hreal]
    dsimp only [BoundaryCondition.extensionSign,sourceBoundaryTerminalAntiDiscriminant]
    ring
  · rw [sourceBoundaryRootDiscriminantBracket_eq hp hp1 h2p .dirichlet φ hreal n w hw,
      sourceDirichletDiscriminantKernel_eq hp hp1 n φ w hw]
    dsimp only [BoundaryCondition.extensionSign,sourceBoundaryTerminalAntiDiscriminant]
    ring

/-- The full moving terminal anti-discriminant has the same filled
kernel, without dividing by its possibly zero terminal value. -/
theorem sourceBracket_dirichletTerminalAnti_discriminant_eq_kernel
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (n : ℤ) (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) (w : ℂ) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n
    sourceBracket h2p (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet n)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ =
      canonicalDiscriminant hp (periodOnePotential φ) μ*
        deriv (canonicalDiscriminant hp (periodOnePotential φ)) μ*
          sourceDirichletDiscriminantKernel hp hp1 n φ w := by
  dsimp only
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n
  let B : ℂ → ℂ := fun z => sourceBracket h2p (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet n)
    (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z) φ
  let A := canonicalDiscriminant hp (periodOnePotential φ) μ*
    deriv (canonicalDiscriminant hp (periodOnePotential φ)) μ
  have he (z : ℂ) (hz : z ≠ μ) : B z = A*sourceDirichletDiscriminantKernel hp hp1 n φ z := by
    rw [sourceDirichletDiscriminantKernel_eq hp hp1 n φ z hz.symm]
    have h := sourceBracket_boundaryTerminalAntiDiscriminant_discriminant_mul
      hp hp1 h2p .dirichlet n φ hreal z
    dsimp only [BoundaryCondition.extensionSign] at h
    have hd := deriv_periodOneBoundaryCharacteristic_at_canonicalRoot_ne_zero_of_realType
      hp hp1 .dirichlet φ hreal n
    rw [← mul_div_assoc]
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hz.symm)) hd)).mpr
    change B z*(2*(μ-z)*deriv (periodOneBoundaryCharacteristic hp hp1 .dirichlet φ) μ) = _
    dsimp only [A,μ]
    linear_combination h
  have hB : ContinuousAt B μ := by
    let L := sourceBivector h2p (fderiv ℂ (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet n) φ)
    have hc := (analyticOnNhd_sourceDiscriminantCotangent_joint hp hp1 (μ,φ) (mem_univ _)).comp
      (f := fun z : ℂ => (z,φ)) (analyticAt_id.prod analyticAt_const)
    exact ((L.analyticAt _).comp hc).continuousAt
  have hC : ContinuousAt (fun z => A*sourceDirichletDiscriminantKernel hp hp1 n φ z) μ :=
    continuousAt_const.mul (analyticOnNhd_sourceDirichletDiscriminantKernel hp hp1 n φ μ (mem_univ _)).continuousAt
  by_cases hw : w = μ
  · subst w
    have hnear : B =ᶠ[𝓝[≠] μ] (fun z => A*sourceDirichletDiscriminantKernel hp hp1 n φ z) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact he z hz
    exact tendsto_nhds_unique
      (hB.tendsto.mono_left nhdsWithin_le_nhds |>.congr' hnear)
      (hC.tendsto.mono_left nhdsWithin_le_nhds)
  · exact he w hw

end NLS.ZakharovShabat
