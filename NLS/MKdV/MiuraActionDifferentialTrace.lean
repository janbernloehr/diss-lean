import NLS.MKdV.MiuraActionFieldTrace

/-! # The nonconstant Fourier cotangent trace of physical actions

The L² field expansion is evaluated at a Fourier mode and divided only
by that nonzero Fourier frequency. Thus the actual scalar action
cotangents recover the nonconstant mass gradient. No action or gap
length is divided out, and arbitrary closed gaps are included.
-/
noncomputable section
open Set Filter Topology NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

/-- The nonconstant mass-gradient coefficient is the convergent physical action-cotangent sum. -/
theorem hasSum_miuraActionDifferentials_fourier (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℤ) (hm : m ≠ 0) :
    HasSum (fun n : ℕ => (2*(Real.pi : ℂ)*(n+1))*
      (fderiv ℂ (miuraL2Action (n+1)) (scalarInclusion a)) (lp.single 2 (-m) 1)) (a.val m) := by
  let d : ℂ := 2*Complex.I*(Real.pi : ℂ)*m
  have hd : d ≠ 0 := mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (Int.cast_ne_zero.mpr hm)
  have hterm (n : ℕ) : l2GardnerDirection (miuraL2Action (n+1)) (scalarInclusion a) m =
      d*(fderiv ℂ (miuraL2Action (n+1)) (scalarInclusion a)) (lp.single 2 (-m) 1) := by
    rw [l2GardnerDirection,l2SpatialDerivative_apply _ (miuraActionGardner_memlp a ha (n+1) (by omega)) m,
      l2ScalarGradient_apply]
  have h := hasSum_miuraGardnerDirections_cotangent a ha (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m)
  change HasSum (fun n : ℕ => (2*(Real.pi : ℂ)*(n+1))*
    l2GardnerDirection (miuraL2Action (n+1)) (scalarInclusion a) m) (periodOneDerivative a m) at h
  simp_rw [hterm] at h
  rw [periodOneDerivative_apply] at h
  have hdiv := h.mul_left d⁻¹
  have hcancel (x y : ℂ) : d⁻¹*(x*(d*y)) = x*y := by
    calc
      _ = x*((d⁻¹*d)*y) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hd,one_mul]
  change HasSum (fun n : ℕ => d⁻¹*((2*(Real.pi : ℂ)*(n+1))*
    (d*(fderiv ℂ (miuraL2Action (n+1)) (scalarInclusion a)) (lp.single 2 (-m) 1))))
      (d⁻¹*(d*a.val m)) at hdiv
  simp only [hcancel] at hdiv
  simpa only [← mul_assoc,inv_mul_cancel₀ hd,one_mul] using hdiv

end NLS.MKdV
