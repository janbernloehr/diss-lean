import NLS.ZakharovShabat.PhysicalOperator

/-! # The cutoff product rule for the original signed physical expression -/
noncomputable section
set_option autoImplicit false
open Complex
namespace NLS.ZakharovShabat

/-- The commutator with multiplication by a scalar cutoff contains only
its derivative and the unchanged opposite physical signs. -/
theorem physicalOperator_smul_of_differentiableAt
    (φ F : ℝ → ℂ × ℂ) (ψ : ℝ → ℂ) (t : ℝ)
    (hψ : DifferentiableAt ℝ ψ t) (hF : DifferentiableAt ℝ F t) :
    physicalOperator φ (fun s => ψ s • F s) t =
      ψ t • physicalOperator φ F t +
        (I * deriv ψ t * (F t).1,-I * deriv ψ t * (F t).2) := by
  have h1 := hψ.hasDerivAt.mul hF.fst.hasDerivAt
  have h2 := hψ.hasDerivAt.mul hF.snd.hasDerivAt
  have hd1 : deriv (fun s => ψ s * (F s).1) t =
      deriv ψ t * (F t).1 + ψ t * deriv (fun s => (F s).1) t := by
    simpa only [Pi.mul_apply] using! h1.deriv
  have hd2 : deriv (fun s => ψ s * (F s).2) t =
      deriv ψ t * (F t).2 + ψ t * deriv (fun s => (F s).2) t := by
    simpa only [Pi.mul_apply] using! h2.deriv
  simp only [physicalOperator,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,hd1,hd2]
  apply Prod.ext <;> dsimp <;> ring

end NLS.ZakharovShabat
