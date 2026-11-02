import NLS.KdV.HillL2Conjugation
import NLS.KdV.HillL2ContourDeformation
import NLS.ComplexAnalysis.TracePrimitiveReflection
import NLS.ComplexAnalysis.RealCircleIntegralReflection

/-! # Reflection and reality of actual rough Hill contour moments

The source-normalized root and primitive reflect with their exact free
sign. Real admissible energies have a purely imaginary primitive and a
unit-modulus multiplier. Circle reflection then proves that the actual
high contour moments at every integer level are real.
-/

noncomputable section
open Set Metric Complex
open scoped ComplexConjugate
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillL2SourceFamily_schwarz (q : Coeff 2) (hreal : IsRealHillPotential q) :
    hillL2SourceFamily.SourceSchwarzData q where
  domain_conj z hz := by
    rcases mem_slitPlane_iff.mp hz with hre | him
    · exact mem_slitPlane_iff.mpr (Or.inl (by simpa only [conj_re] using hre))
    · exact mem_slitPlane_iff.mpr (Or.inr (by simpa only [conj_im,neg_ne_zero] using him))
  free_conj z hz := classicalHillFreePrimitive_conj z hz
  trace_conj s z := hillL2Discriminant_conj _ (hreal.smul_real s) z

theorem mem_hillL2ContinuationDomain_conj (q : Coeff 2) (hreal : IsRealHillPotential q) (z : ℂ)
    (ht : (z,q) ∈ hillL2ContinuationDomain) : (conj z,q) ∈ hillL2ContinuationDomain :=
  (hillL2SourceFamily_schwarz q hreal).continuation_conj z ht

theorem hillL2ContinuedRoot_conj (q : Coeff 2) (hreal : IsRealHillPotential q) (z : ℂ)
    (ht : (z,q) ∈ hillL2ContinuationDomain) :
    hillL2ContinuedRoot (conj z,q) = -conj (hillL2ContinuedRoot (z,q)) :=
  (hillL2SourceFamily_schwarz q hreal).root_conj z ht

theorem hillL2ContinuedPrimitive_conj (q : Coeff 2) (hreal : IsRealHillPotential q) (z : ℂ)
    (ht : (z,q) ∈ hillL2ContinuationDomain) :
    hillL2ContinuedPrimitive (conj z,q) = -conj (hillL2ContinuedPrimitive (z,q)) :=
  (hillL2SourceFamily_schwarz q hreal).primitive_conj z ht

theorem hillL2ContinuedPrimitive_re_eq_zero (q : Coeff 2) (hreal : IsRealHillPotential q) (x : ℝ)
    (ht : ((x : ℂ),q) ∈ hillL2ContinuationDomain) :
    (hillL2ContinuedPrimitive (x,q)).re = 0 := by
  have h := congrArg Complex.re (hillL2ContinuedPrimitive_conj q hreal (x : ℂ) ht)
  simp only [conj_ofReal,neg_re,conj_re] at h
  linarith

theorem norm_hillL2ContinuedMultiplier_eq_one (q : Coeff 2) (hreal : IsRealHillPotential q) (x : ℝ)
    (ht : ((x : ℂ),q) ∈ hillL2ContinuationDomain) :
    ‖hillL2ContinuedMultiplier (x,q)‖ = 1 := by
  rw [← exp_hillL2ContinuedPrimitive _ ht,norm_exp,
    hillL2ContinuedPrimitive_re_eq_zero q hreal x ht,Real.exp_zero]

/-- The literal moment is real on any admissible real-centered circle,
with no assumed action or spectral-sheet data. -/
theorem hillL2CircleMoment_im_eq_zero (q : Coeff 2) (hreal : IsRealHillPotential q)
    (x r : ℝ) (hr : 0 < r)
    (hc : ∀ z ∈ sphere (x : ℂ) r, (z,q) ∈ hillL2ContinuationDomain) (m : ℕ) :
    (hillL2SourceFamily.contourMoment x r m q).im = 0 := by
  have hi := circleIntegral_im_eq_zero_of_anti_conj
    (fun z => z^m*hillL2ContinuedPrimitive (z,q)) x r hr (by
      intro z hz
      rw [hillL2ContinuedPrimitive_conj q hreal z (hc z hz),map_mul,map_pow]
      ring)
  change (-(Real.pi : ℂ)⁻¹ * ∮ z in C((x : ℂ),r), z^m*hillL2ContinuedPrimitive (z,q)).im = 0
  simp only [← ofReal_inv,← ofReal_neg,mul_im,ofReal_re,ofReal_im,hi,mul_zero,zero_mul,add_zero]

theorem hillL2HighContourMoment_im_eq_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ)) (m : ℕ) :
    (hillL2HighContourMoment n m (SpectralWeight.one.toCoeff q)).im = 0 :=
  hillL2CircleMoment_im_eq_zero _ hreal (freeHillValue n) (n : ℝ)
    (by exact_mod_cast (show 0 < n by omega))
    (mem_hillL2ContinuationDomain_high_sphere q hq n hn hcut) m

end NLS.KdV
