import NLS.KdV.HillNormalizedResolvent
import NLS.Articles.KdVPseudomeasures.PeriodicNormalizedPerturbation

/-! The original Appendix C.4 normalized native resolvent, with ONE cutoff
before the entire original rough-potential norm ball and literal source circles. -/
noncomputable section
open Set Metric
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The normalized source pencil acts on the ENTIRE original H1 domain,
with exactly the same original potential distribution. -/
theorem sourcePeriodicNormalizedPencil_eq (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : FourierLebesgueSpace (2:ℝ) (-r) 2) (n : ℕ+) (hlog : 1 < Real.log (n:ℝ)) (z : ℂ)
    (hz : z ∈ sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)) :
    (hillHalfFromBase z).comp
      ((z • singularHillDomainInclusion-singularHillOperator (hillSobolevBaseInclusion r hr1 q)).comp
        (hillHalfToH1 z)) = hillNormalizedPhase z-hillHalfSandwich r (sobolevCoefficients (-r) 2 q) z := by
  have hz' : z ∈ sphere (freeHillValue (n:ℕ):ℂ) (n:ℝ) := by
    rwa [freeHillValue_natCast_complex]
  exact hillNormalizedPencil_eq r hr hr1 (sobolevCoefficients (-r) 2 q) (n:ℕ) n.property hlog z hz'

/-- Actual physical perturbation smallness gives the exact original native
resolvent formula, including its A-lambda*J sign and ENTIRE original base. -/
theorem sourcePeriodicResolventToH1_eq_normalized (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : FourierLebesgueSpace (2:ℝ) (-r) 2) (n : ℕ+) (hlog : 1 < Real.log (n:ℝ)) (z : ℂ)
    (hz : z ∈ sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ))
    (hS : ‖sourcePeriodicNormalizedPerturbation r q z‖ ≤ 1/2) :
    singularHillResolventToH1 (hillSobolevBaseInclusion r hr1 q) z =
      -hillNormalizedResolventToH1 r (sobolevCoefficients (-r) 2 q) z := by
  have hz' : z ∈ sphere (freeHillValue (n:ℕ):ℂ) (n:ℝ) := by
    rwa [freeHillValue_natCast_complex]
  have hsmall : ‖hillHalfSandwich r (sobolevCoefficients (-r) 2 q) z‖ ≤ 1/2 := by
    rwa [sourcePeriodicNormalizedPerturbation,norm_hillPhysicalHalfSandwich] at hS
  exact singularHillResolventToH1_eq_normalized r hr hr1 (sobolevCoefficients (-r) 2 q)
    (n:ℕ) n.property hlog z hz' hsmall

/-- ONE cutoff before EVERY original rough potential in the specified norm
ball, ALL later original positive indices and the ENTIRE literal source circle:
original native resolvent validity, norm-at-most-TWO normalized inverse and
the exact actual native resolvent formula are all PROVED together. -/
theorem exists_uniform_sourcePeriodicNormalizedResolvent (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) 2, ‖q‖ ≤ R →
      ∀ n : ℕ+, N ≤ (n:ℕ) → ∀ z ∈ sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ),
        z ∈ singularHillResolventSet (hillSobolevBaseInclusion r hr1.le q) ∧
        ‖hillNormalizedInverse r (sobolevCoefficients (-r) 2 q) z‖ ≤ 2 ∧
        singularHillResolventToH1 (hillSobolevBaseInclusion r hr1.le q) z =
          -hillNormalizedResolventToH1 r (sobolevCoefficients (-r) 2 q) z := by
  obtain ⟨N,hN,hsmall⟩ := exists_uniform_hillPhysicalHalfSandwich_small r hr hr1 R
  refine ⟨N,hN,?_⟩
  intro q hq n hn z hz
  have hz' : z ∈ sphere (freeHillValue (n:ℕ):ℂ) (n:ℝ) := by
    rwa [freeHillValue_natCast_complex]
  have hlog := (hsmall (n:ℕ) hn).1
  have hS := (hsmall (n:ℕ) hn).2 (sobolevCoefficients (-r) 2 q)
    (by simpa only [LinearIsometryEquiv.norm_map] using hq) z hz'
  rw [norm_hillPhysicalHalfSandwich] at hS
  exact ⟨mem_singularHillResolventSet_of_halfSandwich_small r hr hr1.le
      (sobolevCoefficients (-r) 2 q) (n:ℕ) n.property hlog z hz' hS,
    (hillNormalizedInverse_spec r (sobolevCoefficients (-r) 2 q) (n:ℕ) n.property z hz' hS).2.2,
    singularHillResolventToH1_eq_normalized r hr hr1.le
      (sobolevCoefficients (-r) 2 q) (n:ℕ) n.property hlog z hz' hS⟩

end NLS.Articles.KdVPseudomeasures
