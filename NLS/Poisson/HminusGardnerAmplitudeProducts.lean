import NLS.Poisson.HminusGardnerAlgebra

noncomputable section
set_option autoImplicit false
open Complex
namespace NLS.Poisson
local notation "Hminus" => WeightedCoeff (Weight.sobolev (-1)) 2

/-- Two amplitude-phase products commute when their amplitudes are action
functions, their phases commute, and their cross action rotations vanish. -/
theorem hminusGardnerBracket_amplitude_products_zero
    (A P B Q J K : Hminus → ℂ) (q : Hminus) (α β : ℂ)
    (hA : DifferentiableAt ℂ A q) (hP : DifferentiableAt ℂ P q)
    (hB : DifferentiableAt ℂ B q) (hQ : DifferentiableAt ℂ Q q)
    (hDA : fderiv ℂ A q = α • fderiv ℂ J q)
    (hDB : fderiv ℂ B q = β • fderiv ℂ K q)
    (hAn : A q ≠ 0) (hBn : B q ≠ 0)
    (hJK : hminusGardnerBracket J K q = 0)
    (hPQ : hminusGardnerBracket P Q q = 0)
    (hPK : hminusGardnerBracket (fun a => A a * P a) K q = 0)
    (hQJ : hminusGardnerBracket (fun a => B a * Q a) J q = 0) :
    hminusGardnerBracket (fun a => A a * P a) (fun a => B a * Q a) q = 0 := by
  have hKJ : hminusGardnerBracket K J q = 0 := by
    rw [hminusGardnerBracket_antisymm,hJK,neg_zero]
  have hAK : hminusGardnerBracket A K q = 0 := by
    rw [hminusGardnerBracket_of_fderiv_smul_left A J K q α hDA,hJK,mul_zero]
  have hBJ : hminusGardnerBracket B J q = 0 := by
    rw [hminusGardnerBracket_of_fderiv_smul_left B K J q β hDB,hKJ,mul_zero]
  have hP0 : hminusGardnerBracket P K q = 0 := by
    have he := hminusGardnerBracket_mul_left A P K q hA hP
    rw [hPK,hAK,mul_zero,add_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hAn
  have hQ0 : hminusGardnerBracket Q J q = 0 := by
    have he := hminusGardnerBracket_mul_left B Q J q hB hQ
    rw [hQJ,hBJ,mul_zero,add_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hBn
  apply hminusGardnerBracket_products_zero A P B Q q hA hP hB hQ
  · rw [hminusGardnerBracket_of_fderiv_smul_left A J B q α hDA,
      hminusGardnerBracket_of_fderiv_smul_right J B K q β hDB,hJK,mul_zero,mul_zero]
  · rw [hminusGardnerBracket_of_fderiv_smul_left A J Q q α hDA,
      hminusGardnerBracket_antisymm J Q,hQ0,neg_zero,mul_zero]
  · rw [hminusGardnerBracket_of_fderiv_smul_right P B K q β hDB,hP0,mul_zero]
  · exact hPQ

end NLS.Poisson
