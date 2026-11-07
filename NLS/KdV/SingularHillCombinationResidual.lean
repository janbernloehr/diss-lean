import NLS.KdV.SingularHillPhysical

/-! Exact original native residual for a linear combination of the source
spectral basis. The second coefficient multiplies BOTH residual terms. -/
noncomputable section
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- If G=alpha*f+beta*phi, the native eta equation gives beta*eta*f and
-beta*gamma*phi. In particular beta cannot be omitted from the gamma term. -/
theorem singularHill_combination_residual
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z gamma eta alpha beta : ℂ)
    (f phi : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator q f=z • singularHillDomainInclusion f)
    (hphi : singularHillOperator q phi-z • singularHillDomainInclusion phi=
      -gamma • singularHillDomainInclusion phi+eta • singularHillDomainInclusion f) :
    singularHillOperator q (alpha • f+beta • phi)-z • singularHillDomainInclusion (alpha • f+beta • phi)=
      (beta*eta) • singularHillDomainInclusion f-(beta*gamma) • singularHillDomainInclusion phi := by
  let P := singularHillOperator q-z • singularHillDomainInclusion
  have h0 : P f=0 := sub_eq_zero.mpr hf
  have h1 : P phi= -gamma • singularHillDomainInclusion phi+eta • singularHillDomainInclusion f := hphi
  change P (alpha • f+beta • phi)=_
  rw [map_add,map_smul,map_smul,h0,smul_zero,zero_add,h1]
  module

end NLS.KdV
