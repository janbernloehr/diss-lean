import NLS.ZakharovShabat.SourceBoundaryCanonicalSeparation

/-! # The actual separation differential on the spectral curve

Differentiating the original monodromy characteristic polynomial gives
the differential of the moving discriminant as the signed terminal
anti-discriminant times the actual local Floquet logarithm differential.
Keeping this equation cleared makes it valid at collapsed gaps as well.
The canonical momentum gives the corresponding equation with factor -2.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The signed anti-discriminant is the difference between the two
monodromy eigenvalues at the actual ordinary boundary root. -/
theorem sourceBoundaryFloquetMultiplier_twice_sub_discriminant
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p) :
    2*sourceBoundaryFloquetMultiplier hp hp1 b n φ-
      sourceBoundaryTerminalDiscriminant hp hp1 b n φ =
        extensionSign b*sourceBoundaryTerminalAntiDiscriminant hp hp1 b n φ := by
  unfold sourceBoundaryFloquetMultiplier
  ring

/-- The full actual spectral-curve cotangent equation, with no division
by the terminal anti-discriminant and no open-gap assumption. -/
theorem fderiv_sourceBoundaryTerminalDiscriminant_eq_floquetLog
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    (extensionSign b*sourceBoundaryTerminalAntiDiscriminant hp hp1 b n φ) •
      fderiv ℂ (sourceBoundaryFloquetLogAt hp hp1 b n φ) φ =
        fderiv ℂ (sourceBoundaryTerminalDiscriminant hp hp1 b n) φ := by
  have hρ := (analyticAt_sourceBoundaryFloquetMultiplier_of_realType hp hp1 b n φ hreal).differentiableAt.hasFDerivAt
  have hD := (analyticAt_sourceBoundaryTerminalDiscriminant_of_realType hp hp1 b n φ hreal).differentiableAt.hasFDerivAt
  have hpoly := ((hρ.mul hρ).sub (hD.mul hρ)).add_const (1 : ℂ)
  have heq : (fun ψ : CoeffPair p => sourceBoundaryFloquetMultiplier hp hp1 b n ψ*
      sourceBoundaryFloquetMultiplier hp hp1 b n ψ-
      sourceBoundaryTerminalDiscriminant hp hp1 b n ψ*sourceBoundaryFloquetMultiplier hp hp1 b n ψ+1) =
      (fun _ : CoeffPair p => (0 : ℂ)) := by
    funext ψ
    simpa only [pow_two] using sourceBoundaryFloquetMultiplier_characteristic_polynomial hp hp1 b n ψ
  have hzero := hpoly.fderiv
  simp only [Pi.mul_apply,Pi.sub_apply] at hzero
  rw [heq] at hzero
  simp only [fderiv_fun_const,Pi.zero_apply] at hzero
  rw [fderiv_sourceBoundaryFloquetLogAt hp hp1 b n φ hreal]
  apply ContinuousLinearMap.ext
  intro h
  have hz := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hzero
  simp only [add_apply,sub_apply,smul_apply,smul_eq_mul,zero_apply] at hz ⊢
  apply mul_left_cancel₀ (sourceBoundaryFloquetMultiplier_ne_zero hp hp1 b n φ)
  calc
    _ = (2*sourceBoundaryFloquetMultiplier hp hp1 b n φ-
        sourceBoundaryTerminalDiscriminant hp hp1 b n φ)*
          (fderiv ℂ (sourceBoundaryFloquetMultiplier hp hp1 b n) φ) h := by
      rw [sourceBoundaryFloquetMultiplier_twice_sub_discriminant]
      calc
        _ = (extensionSign b*sourceBoundaryTerminalAntiDiscriminant hp hp1 b n φ)*
          (sourceBoundaryFloquetMultiplier hp hp1 b n φ*
            (sourceBoundaryFloquetMultiplier hp hp1 b n φ)⁻¹)*
              (fderiv ℂ (sourceBoundaryFloquetMultiplier hp hp1 b n) φ) h := by ring
        _ = _ := by rw [mul_inv_cancel₀ (sourceBoundaryFloquetMultiplier_ne_zero hp hp1 b n φ),mul_one]
    _ = _ := by linear_combination -hz

/-- A moving boundary point satisfies the full spectral-curve equation:
the fixed-source discriminant cotangent and the moving-root term both
appear on the right. This holds even when the terminal square root is zero. -/
theorem sourceBoundaryFloquetLog_spectralCurve_cotangent
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    (extensionSign b*sourceBoundaryTerminalAntiDiscriminant hp hp1 b n φ) •
      fderiv ℂ (sourceBoundaryFloquetLogAt hp hp1 b n φ) φ =
        sourceDiscriminantCotangent hp μ φ+
          deriv (canonicalDiscriminant hp (periodOnePotential φ)) μ •
            fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ := by
  rw [fderiv_sourceBoundaryTerminalDiscriminant_eq_floquetLog hp hp1 b n φ hreal,
    fderiv_sourceBoundaryTerminalDiscriminant hp hp1 b n φ hreal]

/-- At a branch terminal the entire moving discriminant cotangent is
zero. The moving-root contribution must still be retained in this equation. -/
theorem fderiv_sourceBoundaryTerminalDiscriminant_eq_zero_at_branch
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hδ : sourceBoundaryTerminalAntiDiscriminant hp hp1 b n φ = 0) :
    fderiv ℂ (sourceBoundaryTerminalDiscriminant hp hp1 b n) φ = 0 := by
  have h := fderiv_sourceBoundaryTerminalDiscriminant_eq_floquetLog hp hp1 b n φ hreal
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L v) h
  simpa only [hδ,mul_zero,zero_mul,smul_apply,smul_eq_mul,zero_apply] using! hv.symm

/-- The canonical momentum version of the full cotangent equation.
Its cleared form remains meaningful at a collapsed periodic gap. -/
theorem sourceBoundaryCanonicalMomentum_spectralCurve_cotangent
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    (extensionSign b*sourceBoundaryTerminalAntiDiscriminant hp hp1 b n φ) •
      fderiv ℂ (sourceBoundaryCanonicalMomentumAt hp hp1 b n φ) φ =
        (-2 : ℂ) • (sourceDiscriminantCotangent hp μ φ+
          deriv (canonicalDiscriminant hp (periodOnePotential φ)) μ •
            fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ) := by
  rw [fderiv_sourceBoundaryCanonicalMomentumAt hp hp1 b n φ hreal,
    smul_comm,sourceBoundaryFloquetLog_spectralCurve_cotangent hp hp1 b n φ hreal]

/-- Applying the actual source bivector to the cotangent equation gives
the spectral-curve relation for any Hamiltonian functional. -/
theorem sourceBracket_boundaryCanonicalMomentum_spectralCurve
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (G : CoeffPair p → ℂ) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    (extensionSign b*sourceBoundaryTerminalAntiDiscriminant hp hp1 b n φ)*
      sourceBracket h2p (sourceBoundaryCanonicalMomentumAt hp hp1 b n φ) G φ =
        -2*(sourceBracket h2p
          (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) μ) G φ+
          deriv (canonicalDiscriminant hp (periodOnePotential φ)) μ*
            sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) G φ) := by
  dsimp only
  have h := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => sourceBivector h2p L (fderiv ℂ G φ))
    (sourceBoundaryCanonicalMomentum_spectralCurve_cotangent hp hp1 b n φ hreal)
  simpa only [sourceBracket,sourceDiscriminantCotangent,map_smul,smul_apply,smul_eq_mul,map_add,add_apply] using h

end NLS.ZakharovShabat
