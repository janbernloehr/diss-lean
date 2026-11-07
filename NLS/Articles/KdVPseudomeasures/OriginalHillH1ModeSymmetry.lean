import NLS.Articles.KdVPseudomeasures.OriginalHillH1ActionHamiltonian
import NLS.SequenceSpaces.FourierRealModePlane
import NLS.FunctionalAnalysis.EvenLineDerivative

/-! Mode reflections of the ACTUAL canonical physical H1 KdV energy.
They apply on the entire signed H^(3/2) domain, including collapsed modes. -/
noncomputable section
open Complex NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

def hillH1ModeCLM (n : ℕ+) :
    ℂ →L[ℝ] RealSignedHilbert (signedStepOrder (1/2) 1) :=
  fourierRealModeCLM _ (Weight.signedSobolev_neg _) n

theorem hillH1ModeCLM_apply (n : ℕ+) (c : ℂ) (k : ℤ) :
    (hillH1ModeCLM n c).val.val.val k=
      (if k=(n:ℤ) then c else 0)+(if k=-(n:ℤ) then (starRingEnd ℂ) c else 0) :=
  fourierRealModeCLM_apply _ _ n c k

theorem hillH1CanonicalHamiltonian_mode_replace
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) (n : ℕ+) (c : ℂ)
    (hc : c*(starRingEnd ℂ) c=z.val.val.val (n:ℤ)*(starRingEnd ℂ) (z.val.val.val (n:ℤ))) :
    hillH1CanonicalHamiltonian (fourierRealModeReplace _ (Weight.signedSobolev_neg _) n z c)=
      hillH1CanonicalHamiltonian z := by
  apply hillH1CanonicalHamiltonian_eq_of_products
  exact fourierRealModeReplace_products _ _ n z c hc

theorem hillH1CanonicalHamiltonian_mode_real_reflection
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) (n : ℕ+) :
    hillH1CanonicalHamiltonian (fourierRealModeReplace _ (Weight.signedSobolev_neg _) n z
      (-(starRingEnd ℂ) (z.val.val.val (n:ℤ))))=hillH1CanonicalHamiltonian z := by
  apply hillH1CanonicalHamiltonian_mode_replace
  rw [map_neg,Complex.conj_conj]
  ring

theorem hillH1CanonicalHamiltonian_mode_imag_reflection
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) (n : ℕ+) :
    hillH1CanonicalHamiltonian (fourierRealModeReplace _ (Weight.signedSobolev_neg _) n z
      ((starRingEnd ℂ) (z.val.val.val (n:ℤ))))=hillH1CanonicalHamiltonian z := by
  apply hillH1CanonicalHamiltonian_mode_replace
  rw [Complex.conj_conj]
  ring

/-- A zero real coordinate makes the physical energy even in its real mode direction. -/
theorem hillH1CanonicalHamiltonian_even_real_mode
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) (n : ℕ+)
    (hz : (z.val.val.val (n:ℤ)).re=0) (t : ℝ) :
    hillH1CanonicalHamiltonian (z+t • hillH1ModeCLM n 1)=
      hillH1CanonicalHamiltonian (z+(-t) • hillH1ModeCLM n 1) := by
  apply hillH1CanonicalHamiltonian_eq_of_products
  intro m
  change (z.val.val.val (m:ℤ)+(t:ℂ)*(hillH1ModeCLM n 1).val.val.val (m:ℤ))*
      (z.val.val.val (-(m:ℤ))+(t:ℂ)*(hillH1ModeCLM n 1).val.val.val (-(m:ℤ)))=
    (z.val.val.val (m:ℤ)+((-t:ℝ):ℂ)*(hillH1ModeCLM n 1).val.val.val (m:ℤ))*
      (z.val.val.val (-(m:ℤ))+((-t:ℝ):ℂ)*(hillH1ModeCLM n 1).val.val.val (-(m:ℤ)))
  rw [hillH1ModeCLM_apply,hillH1ModeCLM_apply]
  have hn : (0:ℤ)<n := by exact_mod_cast n.pos
  have hm : (0:ℤ)<m := by exact_mod_cast m.pos
  by_cases h : (m:ℤ)=(n:ℤ)
  · have hneg : -(n:ℤ)≠(n:ℤ) := by omega
    simp only [h,ite_true,if_neg hneg,map_one,zero_add,mul_one]
    rw [z.property (n:ℤ)]
    apply Complex.ext <;> simp [hz]
    all_goals ring
  · have h1 : (m:ℤ)≠-(n:ℤ) := by omega
    have h2 : -(m:ℤ)≠(n:ℤ) := by omega
    have h3 : -(m:ℤ)≠-(n:ℤ) := by omega
    simp only [if_neg h,if_neg h1,if_neg h2,if_neg h3,mul_zero,add_zero]

theorem hillH1CanonicalHamiltonian_fderiv_real_mode_zero
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) (n : ℕ+)
    (hz : (z.val.val.val (n:ℤ)).re=0) :
    (fderiv ℝ hillH1CanonicalHamiltonian z) (hillH1ModeCLM n 1)=0 := by
  exact @NLS.FunctionalAnalysis.fderiv_apply_eq_zero_of_even_line
    (RealSignedHilbert (signedStepOrder (1/2) 1)) inferInstance inferInstance
    hillH1CanonicalHamiltonian z (hillH1ModeCLM n 1)
    (analyticAt_hillH1CanonicalHamiltonian z).differentiableAt
    (hillH1CanonicalHamiltonian_even_real_mode z n hz)

/-- A zero imaginary coordinate makes the physical energy even in its imaginary mode direction. -/
theorem hillH1CanonicalHamiltonian_even_imag_mode
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) (n : ℕ+)
    (hz : (z.val.val.val (n:ℤ)).im=0) (t : ℝ) :
    hillH1CanonicalHamiltonian (z+t • hillH1ModeCLM n I)=
      hillH1CanonicalHamiltonian (z+(-t) • hillH1ModeCLM n I) := by
  apply hillH1CanonicalHamiltonian_eq_of_products
  intro m
  change (z.val.val.val (m:ℤ)+(t:ℂ)*(hillH1ModeCLM n I).val.val.val (m:ℤ))*
      (z.val.val.val (-(m:ℤ))+(t:ℂ)*(hillH1ModeCLM n I).val.val.val (-(m:ℤ)))=
    (z.val.val.val (m:ℤ)+((-t:ℝ):ℂ)*(hillH1ModeCLM n I).val.val.val (m:ℤ))*
      (z.val.val.val (-(m:ℤ))+((-t:ℝ):ℂ)*(hillH1ModeCLM n I).val.val.val (-(m:ℤ)))
  rw [hillH1ModeCLM_apply,hillH1ModeCLM_apply]
  have hn : (0:ℤ)<n := by exact_mod_cast n.pos
  have hm : (0:ℤ)<m := by exact_mod_cast m.pos
  by_cases h : (m:ℤ)=(n:ℤ)
  · have hneg : -(n:ℤ)≠(n:ℤ) := by omega
    simp only [h,ite_true,if_neg hneg,Complex.conj_I,zero_add]
    rw [z.property (n:ℤ)]
    apply Complex.ext <;> simp [hz]
    all_goals ring
  · have h1 : (m:ℤ)≠-(n:ℤ) := by omega
    have h2 : -(m:ℤ)≠(n:ℤ) := by omega
    have h3 : -(m:ℤ)≠-(n:ℤ) := by omega
    simp only [if_neg h,if_neg h1,if_neg h2,if_neg h3,mul_zero,add_zero]

theorem hillH1CanonicalHamiltonian_fderiv_imag_mode_zero
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) (n : ℕ+)
    (hz : (z.val.val.val (n:ℤ)).im=0) :
    (fderiv ℝ hillH1CanonicalHamiltonian z) (hillH1ModeCLM n I)=0 := by
  exact @NLS.FunctionalAnalysis.fderiv_apply_eq_zero_of_even_line
    (RealSignedHilbert (signedStepOrder (1/2) 1)) inferInstance inferInstance
    hillH1CanonicalHamiltonian z (hillH1ModeCLM n I)
    (analyticAt_hillH1CanonicalHamiltonian z).differentiableAt
    (hillH1CanonicalHamiltonian_even_imag_mode z n hz)


/-- Every direction supported in a collapsed mode annihilates the actual
physical energy differential. This includes both real directions at once. -/
theorem hillH1CanonicalHamiltonian_fderiv_collapsed_mode_zero
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) (n : ℕ+)
    (hz : z.val.val.val (n:ℤ)=0) (c : ℂ) :
    (fderiv ℝ hillH1CanonicalHamiltonian z) (hillH1ModeCLM n c)=0 := by
  have hx := hillH1CanonicalHamiltonian_fderiv_real_mode_zero z n (by simp [hz])
  have hy := hillH1CanonicalHamiltonian_fderiv_imag_mode_zero z n (by simp [hz])
  have he : c=c.re • (1:ℂ)+c.im • I := by
    simpa only [Complex.real_smul,Complex.ofReal_mul,mul_one] using (Complex.re_add_im c).symm
  rw [he,map_add,map_smul,map_smul,map_add,map_smul,map_smul,hx,hy,smul_zero,smul_zero,add_zero]

end NLS.Articles.KdVPseudomeasures
