import NLS.KdV.HillProductDataVariation
import NLS.KdV.HillIndependentPsiPullback
import NLS.ZakharovShabat.SourcePsiCandidateEntireVariation

/-! The actual derivative of the analytic balanced frequency lift.
A zero omitted energy direction fixes its omitted frequency, and the
filled Hill-to-frequency numerator identity differentiates exactly. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

def hillIndependentFrequencyDataVariation (c : ℂ) (d h : lp (fun _ : ℕ+ => ℂ) 2) : Coeff 2 :=
  fderiv ℂ (fun b => hillIndependentFrequencyDisplacement (c,b)) d h

theorem hasDerivAt_hillFrequencyDataLine (c : ℂ) (d h : lp (fun _ : ℕ+ => ℂ) 2)
    (hd : (c,d) ∈ LpSequence.quadraticFrequencyDomain Real.pi) :
    HasDerivAt (fun w : ℂ => hillIndependentFrequencyDisplacement (c,d+w • h))
      (hillIndependentFrequencyDataVariation c d h) 0 := by
  have hp := ((analyticOnNhd_hillIndependentFrequencyDisplacement (c,d) hd).comp
    (f := fun b : lp (fun _ : ℕ+ => ℂ) 2 => (c,b)) (analyticAt_const.prod analyticAt_id)).differentiableAt.hasFDerivAt
  simpa only [zero_add,one_smul] using! hp.comp_hasDerivAt_of_eq 0
    ((hasDerivAt_const (0:ℂ) d).add ((hasDerivAt_id (0:ℂ)).smul_const h)) (by simp)

theorem hasDerivAt_hillFrequencyScalarDataLine (c : ℂ) (d h : lp (fun _ : ℕ+ => ℂ) 2)
    (hd : (c,d) ∈ LpSequence.quadraticFrequencyDomain Real.pi) (k : ℤ) :
    HasDerivAt (fun w : ℂ => hillIndependentFrequency (c,d+w • h) k)
      (hillIndependentFrequencyDataVariation c d h k) 0 := by
  have hv := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_hillFrequencyDataLine c d h hd)
  simpa only [hillIndependentFrequency,displacedRoots] using! hv.const_add ((Real.pi:ℂ)*k)

theorem hillFrequencyDataVariation_omitted_zero (c : ℂ) (d h : lp (fun _ : ℕ+ => ℂ) 2)
    (hd : (c,d) ∈ LpSequence.quadraticFrequencyDomain Real.pi) (n : ℕ+)
    (hβ : hillIndependentFrequency (c,d) ((n:ℕ):ℤ) ≠ 0) (hn : h n = 0) :
    hillIndependentFrequencyDataVariation c d h ((n:ℕ):ℤ) = 0 := by
  have hl : HasDerivAt (fun w : ℂ => hillIndependentFrequency (c,d+w • h) ((n:ℕ):ℤ)^2)
      (2*hillIndependentFrequency (c,d) ((n:ℕ):ℤ)*hillIndependentFrequencyDataVariation c d h ((n:ℕ):ℤ)) 0 := by
    simpa only [Pi.pow_apply,zero_smul,add_zero,Nat.reduceSub,pow_one] using!
      (hasDerivAt_hillFrequencyScalarDataLine c d h hd ((n:ℕ):ℤ)).pow 2
  have hv := (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 n).hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_const (0:ℂ) d).add ((hasDerivAt_id (0:ℂ)).smul_const h))
  have hr : HasDerivAt (fun w : ℂ => ((Real.pi:ℂ)*(n:ℕ))^2+(n:ℕ)*(d+w • h) n+c)
      (((n:ℕ):ℂ)*h n) 0 := by
    simpa only [zero_add,one_smul] using!
      (((hv.const_mul ((n:ℕ):ℂ)).const_add (((Real.pi:ℂ)*(n:ℕ))^2)).add_const c)
  have he : (fun w : ℂ => hillIndependentFrequency (c,d+w • h) ((n:ℕ):ℤ)^2) =
      (fun w : ℂ => ((Real.pi:ℂ)*(n:ℕ))^2+(n:ℕ)*(d+w • h) n+c) := by
    funext w
    exact hillIndependentFrequency_positive_sq (c,d+w • h) n
  rw [he] at hl
  have hh := hl.unique hr
  rw [hn,mul_zero] at hh
  exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero (by norm_num) hβ)

theorem hillEnergyProductDataVariation_frequency_filled (n : ℕ+) (c : ℂ)
    (d h : lp (fun _ : ℕ+ => ℂ) 2) (hd : (c,d) ∈ LpSequence.quadraticFrequencyDomain Real.pi)
    (hβ : hillIndependentFrequency (c,d) ((n:ℕ):ℤ) ≠ 0) (hn : h n = 0) (z : ℂ) :
    (hillIndependentFrequency (c,d) ((n:ℕ):ℤ)+z)*(2*z*hillEnergyProductDataVariation n d h (z^2-c)) =
      ((Real.pi:ℂ)*(n:ℕ))^2*sourcePsiCandidateVariation ((n:ℕ):ℤ)
        (hillIndependentFrequencyDisplacement (c,d)) (hillIndependentFrequencyDataVariation c d h) z := by
  have hzero := hillFrequencyDataVariation_omitted_zero c d h hd n hβ hn
  have hl : HasDerivAt (fun w : ℂ => (hillIndependentFrequency (c,d+w • h) ((n:ℕ):ℤ)+z)*
      (2*z*hillEnergySequenceProduct n (z^2-c,d+w • h)))
      ((hillIndependentFrequency (c,d) ((n:ℕ):ℤ)+z)*(2*z*hillEnergyProductDataVariation n d h (z^2-c))) 0 := by
    simpa only [zero_smul,add_zero,hzero,zero_mul,zero_add] using!
      ((hasDerivAt_hillFrequencyScalarDataLine c d h hd ((n:ℕ):ℤ)).add_const z).mul
        ((hasDerivAt_hillEnergyProductDataLine n (z^2-c) d h).const_mul (2*z))
  have hs := ((analyticOnNhd_sourcePsiCandidate (by norm_num) (by norm_num) ((n:ℕ):ℤ)
    (z,hillIndependentFrequencyDisplacement (c,d)) (mem_univ _)).comp
      (f := fun b : Coeff 2 => (z,b)) (analyticAt_const.prod analyticAt_id)).differentiableAt.hasFDerivAt
  have hc := hs.comp_hasDerivAt_of_eq 0 (hasDerivAt_hillFrequencyDataLine c d h hd) (by simp)
  have hr := hc.const_mul (((Real.pi:ℂ)*(n:ℕ))^2)
  have he : (fun w : ℂ => (hillIndependentFrequency (c,d+w • h) ((n:ℕ):ℤ)+z)*
      (2*z*hillEnergySequenceProduct n (z^2-c,d+w • h))) =
      (fun w : ℂ => ((Real.pi:ℂ)*(n:ℕ))^2*sourcePsiCandidate ((n:ℕ):ℤ)
        (z,hillIndependentFrequencyDisplacement (c,d+w • h))) :=
    funext (fun w => hillEnergyProduct_independent_candidate_filled n c (d+w • h) z)
  rw [he] at hl
  have hh := hl.unique hr
  exact hh

end NLS.KdV
