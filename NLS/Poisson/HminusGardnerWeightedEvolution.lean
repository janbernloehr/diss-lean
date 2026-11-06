import NLS.Poisson.GardnerHamiltonianTransport

noncomputable section
set_option autoImplicit false
open Complex
namespace NLS.Poisson
local notation "Hminus" => WeightedCoeff (Weight.sobolev (-1)) 2

/-- Exact bracket evolution follows from the differentials of two
Hamiltonian rotation laws; no flow invariance premise is assumed. -/
theorem hminusGardnerBracket_weighted_hamiltonian_derivative
    (F G J : Hminus → ℂ) (q : Hminus) (α β : ℂ)
    (hF : AnalyticAt ℂ F q) (hG : AnalyticAt ℂ G q) (hJ : AnalyticAt ℂ J q)
    (hFJ : fderiv ℂ (hminusGardnerBracket F J) q = α • fderiv ℂ F q)
    (hGJ : fderiv ℂ (hminusGardnerBracket G J) q = β • fderiv ℂ G q) :
    (fderiv ℂ (hminusGardnerBracket F G) q) (gardnerHamiltonianVector J q) =
      (α + β) * hminusGardnerBracket F G q := by
  rw [hminusGardnerBracket_hamiltonian_derivative F G J q hF hG hJ,hFJ,hGJ]
  simp only [smul_apply,smul_eq_mul,fderiv_apply_gardnerHamiltonianVector]
  rw [hminusGardnerBracket_antisymm G F]
  ring

end NLS.Poisson
