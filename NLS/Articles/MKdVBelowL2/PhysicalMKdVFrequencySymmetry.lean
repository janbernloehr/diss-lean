import NLS.Articles.MKdVBelowL2.PhysicalFourthFourierApproximation
import NLS.ZakharovShabat.SourceSobolevFourthDiagonalFrequency

/-! # Odd H₄ frequency on the full physical mKdV domain

The independently defined native physical derivative supplies the symmetry.
Original diagonal Fourier cutoffs, coefficient-preserving native representatives
and continuity extend it to every finite Fourier–Lebesgue exponent p>1.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original physical normalized derivative is odd on every native
mKdV datum, in the same fixed Birkhoff family as Theorem 1.2. -/
theorem physicalSobolevFourthFrequency_odd_of_diagonal
    (a : NativeFourthSobolevSource) (ha : fourthSobolevPhysicalInput a ∈ physicalMKdVSubspace 2)
    (n : ℤ) : physicalSobolevFourthFrequency a (-n) = -physicalSobolevFourthFrequency a n := by
  have hdiag := (mem_physicalMKdVSubspace_iff_source (fourthSobolevPhysicalInput a)).mp ha
  change (physicalCoefficients (fourthSobolevPhysicalInput a).val).fst =
    (physicalCoefficients (fourthSobolevPhysicalInput a).val).snd at hdiag
  rw [fourthSobolevPhysicalInput_coefficients] at hdiag
  exact (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex.normalizedSobolevFourthFrequency_odd_of_diagonal
    a hdiag n

/-- Each original physical normalized frequency is continuous on the full
real source, including closed gaps. -/
theorem continuous_physicalFourthFrequencyCandidate_real
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    Continuous (fun u : PhysicalRealInput p => physicalFourthFrequencyCandidate hp hp1 n u.val) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  exact (((physicalFourthFrequencyCandidate_analytic hp hp1 n u.val
    ((physicalFourthCandidateDomain_open_real hp hp1).2 u)).restrictScalars (𝕜 := ℝ)).comp
      ((physicalRealSubspace p).subtypeL.analyticAt u)).continuousAt

/-- Corollary 6.1: the actual normalized H₄ extension is odd at every
physical real mKdV input and every signed index, for all finite p>1. -/
theorem physicalMKdV_fourthFrequencyCandidate_odd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (u : PhysicalMKdVInput p) (n : ℤ) :
    physicalFourthFrequencyCandidate hp hp1 (-n) u.val.val =
      -physicalFourthFrequencyCandidate hp hp1 n u.val.val := by
  have hclosed : IsClosed {v : PhysicalRealInput p |
      physicalFourthFrequencyCandidate hp hp1 (-n) v.val =
        -physicalFourthFrequencyCandidate hp hp1 n v.val} :=
    isClosed_eq (continuous_physicalFourthFrequencyCandidate_real hp hp1 (-n))
      (continuous_physicalFourthFrequencyCandidate_real hp hp1 n).neg
  apply hclosed.mem_of_tendsto (tendsto_physicalMKdVTruncate hp u.val)
  apply Eventually.of_forall
  intro N
  obtain ⟨a,ha,hb,hdiag⟩ := exists_nativeFourth_physicalMKdVTruncate N u
  change physicalFourthFrequencyCandidate hp hp1 (-n) (physicalMKdVTruncate N u.val).val =
    -physicalFourthFrequencyCandidate hp hp1 n (physicalMKdVTruncate N u.val).val
  rw [physicalFourthFrequencyCandidate_eq_sobolev_of_same_distributions hp hp1 _ a ⟨ha,hb⟩ (-n),
    physicalFourthFrequencyCandidate_eq_sobolev_of_same_distributions hp hp1 _ a ⟨ha,hb⟩ n]
  exact physicalSobolevFourthFrequency_odd_of_diagonal a hdiag n

/-- The actual normalized zero-mode frequency is zero on every rough
physical mKdV datum. No assumption on its selected action is required. -/
theorem physicalMKdV_fourthFrequencyCandidate_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (u : PhysicalMKdVInput p) :
    physicalFourthFrequencyCandidate hp hp1 0 u.val.val = 0 := by
  have h := physicalMKdV_fourthFrequencyCandidate_odd hp hp1 u 0
  simp only [neg_zero] at h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  apply Complex.ext <;> simp only [Complex.neg_re,Complex.neg_im,Complex.zero_re,Complex.zero_im] at * <;> linarith

/-- The complex weighted realization of Theorem 1.3 retains odd indexing
on the physical diagonal in every one of its finite target exponents. -/
theorem physicalMKdV_fourthFrequencySequence_odd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (hr : r ≠ ⊤) (hr1 : 1 < r) (hpr : ENNReal.ofReal (p.toReal/2) ≤ r)
    (u : PhysicalMKdVInput p) (n : ℤ) :
    (physicalFourthFrequencySequence hp hp1 r u.val.val).val (-n) =
      -(physicalFourthFrequencySequence hp hp1 r u.val.val).val n := by
  have hu := (physicalFourthCandidateDomain_open_real hp hp1).2 u.val
  rw [(physicalFourthFrequencySequence_analytic hp hp1 r hr hr1 hpr).1 _ hu (-n),
    (physicalFourthFrequencySequence_analytic hp hp1 r hr hr1 hpr).1 _ hu n]
  exact physicalMKdV_fourthFrequencyCandidate_odd hp hp1 u n

/-- The actual real weighted sequence has the same symmetry, with the
original raw coefficients retained in its real target. -/
theorem physicalMKdV_realFourthFrequencySequence_odd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (hr : r ≠ ⊤) (hr1 : 1 < r) (hpr : ENNReal.ofReal (p.toReal/2) ≤ r)
    (u : PhysicalMKdVInput p) (n : ℤ) :
    (physicalRealFourthFrequencySequence hp hp1 r u.val).val.val (-n) =
      -(physicalRealFourthFrequencySequence hp hp1 r u.val).val.val n := by
  rw [physicalRealFourthFrequencySequence_apply hp hp1 r hr hr1 hpr u.val (-n),
    physicalRealFourthFrequencySequence_apply hp hp1 r hr hr1 hpr u.val n]
  exact physicalMKdV_fourthFrequencyCandidate_odd hp hp1 u n

/-- The actual cubic-plus-normalized rotation frequency has the same odd
signed-index symmetry on the full original physical mKdV domain. -/
theorem physicalMKdV_fourthSourcePhaseFrequency_odd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (u : PhysicalMKdVInput p) (n : ℤ) :
    (fourthSourcePhaseFrequency hp hp1).frequency (physicalRealCoefficientsCL u.val) (-n) =
      -(fourthSourcePhaseFrequency hp hp1).frequency (physicalRealCoefficientsCL u.val) n := by
  have h := congrArg Complex.re (physicalMKdV_fourthFrequencyCandidate_odd hp hp1 u n)
  change (fourthFrequencyCandidate (fourthMomentChart hp hp1).atlas (-n)
      (physicalRealCoefficientsCL u.val).val).re =
    -(fourthFrequencyCandidate (fourthMomentChart hp hp1).atlas n (physicalRealCoefficientsCL u.val).val).re at h
  change (2*Real.pi*((-n:ℤ):ℝ))^3+_ = -((2*Real.pi*n)^3+_)
  rw [h]
  push_cast
  ring

end NLS.Articles.MKdVBelowL2
