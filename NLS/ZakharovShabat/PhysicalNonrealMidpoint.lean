import NLS.ZakharovShabat.PhysicalPeriodicMidpointGap
import NLS.ZakharovShabat.PhysicalConstantPeriodicSpectrum
import NLS.ZakharovShabat.ClassicalSignedDiscriminant

/-! # An explicit physical potential with a nonreal periodic midpoint -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Square-summable displacements force both labels of some pair into the right half-plane. -/
theorem exists_physicalPeriodicEndpoints_re_pos (u : IntervalPairL2) :
    ∃ n : ℤ, 0 < (physicalPeriodicLeft u n).re ∧ 0 < (physicalPeriodicRight u n).re := by
  let a : Coeff 2 := ⟨fun n => physicalPeriodicLeft u n-(Real.pi : ℂ)*n,
    (physicalPeriodicEndpoints_spec u).left_displacement⟩
  let b : Coeff 2 := ⟨fun n => physicalPeriodicRight u n-(Real.pi : ℂ)*n,
    (physicalPeriodicEndpoints_spec u).right_displacement⟩
  obtain ⟨N,hN⟩ := exists_nat_gt ((‖a‖+‖b‖)/Real.pi)
  have hlarge : ‖a‖+‖b‖ < Real.pi*N := by
    exact (div_lt_iff₀ Real.pi_pos).mp hN |>.trans_eq (mul_comm _ _)
  have ha := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) a (N : ℤ)
  have hb := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) b (N : ℤ)
  have hla := (abs_le.mp (Complex.abs_re_le_norm (a (N : ℤ)))).1
  have hlb := (abs_le.mp (Complex.abs_re_le_norm (b (N : ℤ)))).1
  change ‖physicalPeriodicLeft u (N : ℤ)-(Real.pi : ℂ)*(N : ℤ)‖ ≤ ‖a‖ at ha
  change ‖physicalPeriodicRight u (N : ℤ)-(Real.pi : ℂ)*(N : ℤ)‖ ≤ ‖b‖ at hb
  change -‖physicalPeriodicLeft u (N : ℤ)-(Real.pi : ℂ)*(N : ℤ)‖ ≤
    (physicalPeriodicLeft u (N : ℤ)-(Real.pi : ℂ)*(N : ℤ)).re at hla
  change -‖physicalPeriodicRight u (N : ℤ)-(Real.pi : ℂ)*(N : ℤ)‖ ≤
    (physicalPeriodicRight u (N : ℤ)-(Real.pi : ℂ)*(N : ℤ)).re at hlb
  simp only [Int.cast_natCast] at ha hb
  simp at hla hlb
  refine ⟨N,?_,?_⟩
  · have := norm_nonneg b
    linarith
  · have := norm_nonneg a
    linarith

/-- Every spectral point of the actual constant potential (1,i) satisfies 2 Re(z) Im(z)=1. -/
theorem constant_one_I_spectral_re_im (z : ℂ)
    (hz : z ∈ physicalPeriodicSpectrum (periodOnePair (sourceConstantPotential (p := 2) 1 Complex.I))) :
    2*z.re*z.im = 1 := by
  obtain ⟨k,hk⟩ := (mem_physicalPeriodicSpectrum_constant_iff 1 Complex.I z one_ne_zero).mp hz
  have hi := congrArg Complex.im hk
  simp [pow_two,Complex.mul_im] at hi
  nlinarith

/-- The p.18 complex-midpoint assertion holds for the explicit physical constant potential (1,i). -/
theorem exists_physical_nonreal_midpoint_constant :
    ∃ n : ℤ, (physicalPeriodicMidpoint
      (sourcePhysicalL2 (sourceConstantPotential (p := 2) 1 Complex.I)) n).im ≠ 0 := by
  let u := sourcePhysicalL2 (sourceConstantPotential (p := 2) 1 Complex.I)
  obtain ⟨n,hl,hr⟩ := exists_physicalPeriodicEndpoints_re_pos u
  have hm (z : ℂ) (hz : physicalPeriodicLeft u n = z ∨ physicalPeriodicRight u n = z) :
      2*z.re*z.im = 1 := by
    apply constant_one_I_spectral_re_im
    have h := (physicalPeriodicSpectrum_iff_endpoint u z).mpr ⟨n,hz⟩
    simpa only [u,← sourcePhysicalL2Equiv_apply,LinearIsometryEquiv.symm_apply_apply] using h
  have hL := hm (physicalPeriodicLeft u n) (Or.inl rfl)
  have hR := hm (physicalPeriodicRight u n) (Or.inr rfl)
  have hLi : 0 < (physicalPeriodicLeft u n).im := by nlinarith
  have hRi : 0 < (physicalPeriodicRight u n).im := by nlinarith
  refine ⟨n,?_⟩
  change (physicalPeriodicMidpoint u n).im ≠ 0
  simp only [physicalPeriodicMidpoint,Complex.div_ofNat_im,Complex.add_im]
  linarith

end NLS.ZakharovShabat
