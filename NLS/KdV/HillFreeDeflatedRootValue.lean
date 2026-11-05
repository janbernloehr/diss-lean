import NLS.KdV.HillFreeStateCurves
import NLS.KdV.HillDeflatedCanonicalRoot
import NLS.ZakharovShabat.SourceStandardRootAlgebra

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The ORIGINAL free canonical root factors through the selected collapsed
endpoint with its original sign, on the entire complex energy plane. -/
theorem hillFreeDeflatedRoot_factorization (n : ℕ) (hn : 1 ≤ n) (E : ℂ) :
    ((freeHillValue n : ℂ)-E)*hillDeflatedEnergyCanonicalRoot 0 h0q h0r n E =
      -2*I*Complex.sin (Complex.sqrt E) := by
  have hh := hillEnergyCanonicalRootProduct_eq_endpoint_mul_deflated 0 h0q h0r n hn E
  obtain ⟨hl,hu⟩ := hillFreeGapEndpoints h0q h0r n hn
  rw [hillEnergyCanonicalRootProduct_zero h0q h0r E,hl,hu] at hh
  have he : endpointRoot (freeHillValue n : ℂ) (freeHillValue n : ℂ) E = (freeHillValue n : ℂ)-E := by
    simp only [endpointRoot,sub_self,zero_pow (by norm_num : 2 ≠ 0),normalizedStandardRoot_zeroGap]
    ring
  rw [he] at hh
  exact hh.symm

/-- The exact ORIGINAL deflated-root value at EVERY free positive energy.
Its alternating complex sign is derived from the canonical root product. -/
theorem hillDeflatedEnergyCanonicalRoot_free_value (n : ℕ) (hn : 1 ≤ n) :
    hillDeflatedEnergyCanonicalRoot 0 h0q h0r n (freeHillValue n : ℂ) =
      I*(-1 : ℂ)^n/((n : ℂ)*Real.pi) := by
  let E : ℂ := freeHillValue n
  let z : ℂ := (n : ℂ)*Real.pi
  let B := hillDeflatedEnergyCanonicalRoot 0 h0q h0r n
  have hz : z ≠ 0 := mul_ne_zero
    (by exact_mod_cast (by omega : n ≠ 0)) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hfilled : E ∈ hillGapFilledDomain 0 h0q h0r n := by
    rw [show E = (hillRealLabels 0 h0q h0r (2*n-1) : ℂ) by
      rw [(hillFreeGapEndpoints h0q h0r n hn).1]]
    exact hillGapSegment_subset_filledDomain 0 h0q h0r n hn (left_mem_segment ℝ _ _)
  have hslit : E ∈ Complex.slitPlane := by
    have hh := hillGroundShift_mem_slitPlane_of_mem_filledDomain 0 h0q h0r n E hfilled
    simpa only [hillRealLabels_zero_ground h0q h0r,ofReal_zero,sub_zero] using hh
  have hsq : AnalyticAt ℂ Complex.sqrt E :=
    Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds hslit)
  have heq : (fun w : ℂ => (Complex.sqrt w)^2) = id := funext complex_sqrt_sq
  have hpow := hsq.differentiableAt.hasDerivAt.pow 2
  have hident : HasDerivAt (fun w : ℂ => (Complex.sqrt w)^2) 1 E := by
    rw [heq]
    exact hasDerivAt_id E
  have hval := hpow.unique hident
  simp only [Nat.reduceSub,pow_one] at hval
  have hEz : Complex.sqrt E = z := hillFreeGap_sqrt n
  rw [hEz] at hval
  have hd : deriv Complex.sqrt E = (2*z)⁻¹ := by
    rw [←one_div]
    apply (eq_div_iff (mul_ne_zero (by norm_num) hz)).mpr
    linear_combination hval
  have hsqrt : HasDerivAt Complex.sqrt ((2*z)⁻¹) E := by
    rw [←hd]
    exact hsq.differentiableAt.hasDerivAt
  have hF := hsqrt.csin.const_mul (-2*I)
  rw [hEz] at hF
  have hB : AnalyticAt ℂ B E := analyticOnNhd_hillDeflatedEnergyCanonicalRoot 0 h0q h0r n E hfilled
  have hP := ((hasDerivAt_const E E).sub (hasDerivAt_id E)).mul hB.differentiableAt.hasDerivAt
  have he : (fun w : ℂ => (E-w)*B w) = (fun w => -2*I*Complex.sin (Complex.sqrt w)) := by
    funext w
    exact hillFreeDeflatedRoot_factorization h0q h0r n hn w
  have hPd : HasDerivAt (fun w : ℂ => (E-w)*B w) (-B E) E := by
    convert! hP using 1
    dsimp
    ring
  rw [he] at hPd
  have hv := hPd.unique hF
  have hc : Complex.cos z = (-1 : ℂ)^n := by
    dsimp only [z]
    rw [←ofReal_natCast,←ofReal_mul,←ofReal_cos,Real.cos_nat_mul_pi]
    norm_cast
  rw [hc] at hv
  change B E = I*(-1 : ℂ)^n/z
  field_simp [hz] at hv ⊢
  linear_combination -hv

end NLS.KdV
