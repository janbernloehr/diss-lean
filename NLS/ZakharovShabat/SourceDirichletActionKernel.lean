import NLS.ZakharovShabat.SourceAntiDiscriminantActionPoisson
import NLS.ZakharovShabat.SourceBoundaryTerminalDifferential
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # The actual Dirichlet action flow through branch terminals

The moving Dirichlet root and terminal anti-discriminant share one
normalized action contour kernel. The root velocity contains the
terminal anti-discriminant, while its full moving velocity contains
Delta times its spectral derivative. No terminal square root is divided
out, so the formulas also include periodic and collapsed terminals.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual Dirichlet interpolation kernel integrated over an actual
indexed action circle. Its only terminal denominator is the simple
Dirichlet characteristic derivative. -/
def sourceDirichletActionKernel (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (ch : SourceRealActionBallChart hp hp1 k) (φ : CoeffPair p) : ℂ :=
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n;
  -(Real.pi : ℂ)⁻¹*(2*deriv (periodOneBoundaryCharacteristic hp hp1 .dirichlet φ) μ)⁻¹*
    (∮ w in C(ch.spectralCenter,ch.spectralRadius),
      (sourceCanonicalRoot hp hp1 φ w)⁻¹*periodOneBoundaryCharacteristic hp hp1 .dirichlet φ w/(μ-w))

/-- Differentiate the original spectral identity before evaluating at
an actual Dirichlet zero. This does not require a nonzero square root. -/
theorem sourceDiscriminant_mul_deriv_at_canonicalDirichletRoot
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n
    canonicalDiscriminant hp (periodOnePotential φ) μ*
      deriv (canonicalDiscriminant hp (periodOnePotential φ)) μ =
      sourceAntiDiscriminantCandidate hp hp1 φ μ*
        deriv (sourceAntiDiscriminantCandidate hp hp1 φ) μ-
      2*deriv (periodOneBoundaryCharacteristic hp hp1 .dirichlet φ) μ*
        periodOneBoundaryCharacteristic hp hp1 .neumann φ μ := by
  dsimp only
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n
  have hΔ := (analyticOnNhd_canonicalDiscriminant hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) μ (mem_univ _)).differentiableAt.hasDerivAt
  have hδ := (analyticOnNhd_sourceAntiDiscriminantCandidate hp hp1 φ μ
    (mem_univ _)).differentiableAt.hasDerivAt
  have hD := (analyticOnNhd_periodOneBoundaryCharacteristic hp hp1 .dirichlet φ μ
    (mem_univ _)).differentiableAt.hasDerivAt
  have hN := (analyticOnNhd_periodOneBoundaryCharacteristic hp hp1 .neumann φ μ
    (mem_univ _)).differentiableAt.hasDerivAt
  have heq : (fun z => (canonicalDiscriminant hp (periodOnePotential φ) z)^2-4) =
      (fun z => (sourceAntiDiscriminantCandidate hp hp1 φ z)^2-
        4*periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z*
          periodOneBoundaryCharacteristic hp hp1 .neumann φ z) := by
    funext z
    exact sourceDiscriminant_sq_sub_four hp hp1 φ z
  have hd := (hΔ.pow 2).sub_const (4 : ℂ)
  have hn := (hδ.pow 2).fun_sub ((hD.const_mul (4 : ℂ)).fun_mul hN)
  simp only [Pi.pow_apply] at hd hn
  have he := congrArg (fun f : ℂ → ℂ => deriv f μ) heq
  rw [hd.deriv,hn.deriv] at he
  rw [periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero hp hp1 .dirichlet φ n] at he
  linear_combination he/2

/-- The actual root/action velocity is delta times the common contour
kernel, including when delta is zero. -/
theorem sourceBracket_dirichletRoot_action_eq_kernel
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (n k : ℤ) (ch : SourceRealActionBallChart hp hp1 k)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hφ : φ ∈ ball ch.center ch.radius) :
    sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
      (sourceComplexAction hp hp1 k) φ =
      sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet n φ*
        sourceDirichletActionKernel hp hp1 n k ch φ := by
  rw [sourceBracket_boundaryRoot_action_eq_characteristic_circle hp hp1 h2p .dirichlet n k ch φ hreal hφ]
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n
  let d := deriv (periodOneBoundaryCharacteristic hp hp1 .dirichlet φ) μ
  have hi : (∮ w in C(ch.spectralCenter,ch.spectralRadius),
      (sourceCanonicalRoot hp hp1 φ w)⁻¹*
        (BoundaryCondition.extensionSign .dirichlet*sourceAntiDiscriminantCandidate hp hp1 φ μ*
          periodOneBoundaryCharacteristic hp hp1 .dirichlet φ w)/(2*(μ-w)*d)) =
      sourceAntiDiscriminantCandidate hp hp1 φ μ*(2*d)⁻¹*
        (∮ w in C(ch.spectralCenter,ch.spectralRadius),
          (sourceCanonicalRoot hp hp1 φ w)⁻¹*periodOneBoundaryCharacteristic hp hp1 .dirichlet φ w/(μ-w)) := by
    rw [← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr ch.spectralRadius_pos.le
    intro w _
    dsimp only [BoundaryCondition.extensionSign]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hi]
  dsimp only [sourceDirichletActionKernel,sourceBoundaryTerminalAntiDiscriminant,μ,d]
  ring

/-- The fixed-parameter anti-discriminant velocity at the selected
Dirichlet root is expressed by the same actual contour kernel. -/
theorem sourceBracket_anti_action_at_dirichletRoot_eq_kernel
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (n k : ℤ) (ch : SourceRealActionBallChart hp hp1 k)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hφ : φ ∈ ball ch.center ch.radius) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n
    sourceBracket h2p (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ μ)
      (sourceComplexAction hp hp1 k) φ =
      -2*deriv (periodOneBoundaryCharacteristic hp hp1 .dirichlet φ) μ*
        periodOneBoundaryCharacteristic hp hp1 .neumann φ μ*
          sourceDirichletActionKernel hp hp1 n k ch φ := by
  dsimp only
  rw [sourceBracket_anti_action_at_canonicalDirichletRoot hp hp1 h2p n k ch φ hreal hφ]
  dsimp only [sourceDirichletActionKernel]
  have hd := deriv_periodOneBoundaryCharacteristic_at_canonicalRoot_ne_zero_of_realType
    hp hp1 .dirichlet φ hreal n
  field_simp [hd]

/-- Retaining the moving spectral parameter gives the full terminal
anti-discriminant/action flow at every terminal, including branches. -/
theorem sourceBracket_dirichletTerminalAnti_action_eq_kernel
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (n k : ℤ) (ch : SourceRealActionBallChart hp hp1 k)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hφ : φ ∈ ball ch.center ch.radius) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n
    sourceBracket h2p (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet n)
      (sourceComplexAction hp hp1 k) φ =
      canonicalDiscriminant hp (periodOnePotential φ) μ*
        deriv (canonicalDiscriminant hp (periodOnePotential φ)) μ*
          sourceDirichletActionKernel hp hp1 n k ch φ := by
  dsimp only
  rw [sourceBracket,fderiv_sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet n φ hreal]
  simp only [map_add,add_apply,map_smul,smul_apply,smul_eq_mul]
  change sourceBracket h2p (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n))
      (sourceComplexAction hp hp1 k) φ+
    deriv (sourceAntiDiscriminantCandidate hp hp1 φ)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n)*
      sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
        (sourceComplexAction hp hp1 k) φ = _
  rw [sourceBracket_anti_action_at_dirichletRoot_eq_kernel hp hp1 h2p n k ch φ hreal hφ,
    sourceBracket_dirichletRoot_action_eq_kernel hp hp1 h2p n k ch φ hreal hφ,
    sourceDiscriminant_mul_deriv_at_canonicalDirichletRoot hp hp1 φ n]
  dsimp only [sourceBoundaryTerminalAntiDiscriminant]
  ring

end NLS.ZakharovShabat
