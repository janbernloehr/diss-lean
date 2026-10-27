import NLS.Fourier.PeriodicFourierLebesgueSeries
import NLS.SequenceSpaces.SobolevFullDuality

/-! # Full Sobolev duality on original periodic distributions

For every positive period, real order, and finite source exponent, the full
continuous dual is isometrically the opposite-order Fourier–Lebesgue space.
The representative is an actual smooth-test distribution. The physical
bilinear formula reverses one Fourier index and retains the normalized action.
The source endpoint p = 1 is included; p = infinity is not asserted.
-/
noncomputable section
open scoped ENNReal SchwartzMap
namespace NLS.Fourier.PeriodicFourierLebesgue
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- Exact coefficients of the original Sobolev distribution space. -/
def sobolevCoefficients (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    FourierLebesgueSpace L s p ≃ₗᵢ[ℂ] WeightedCoeff (Weight.sobolev s) p :=
  coefficientsIsometry _ _ (Weight.hasTemperedInverse_sobolev s)

@[simp] theorem sobolevCoefficients_apply (s : ℝ)
    (u : FourierLebesgueSpace L s p) (n : ℤ) :
    (sobolevCoefficients s p u).val n = u.val (mode (-n)) := rfl

/-- The whole continuous dual, with no restriction to coefficient evaluations. -/
def sobolevDualEquiv (s : ℝ) (hp : p ≠ ⊤) :
    FourierLebesgueSpace L (-s) q ≃L[ℂ] (FourierLebesgueSpace L s p →L[ℂ] ℂ) :=
  (sobolevCoefficients (-s) q).toContinuousLinearEquiv.trans
    ((WeightedCoeff.sobolevDualityIsometry s hp).toContinuousLinearEquiv.trans
      ((sobolevCoefficients s p).symm.toContinuousLinearEquiv.arrowCongr
        (ContinuousLinearEquiv.refl ℂ ℂ)))

theorem sobolevDualEquiv_apply (s : ℝ) (hp : p ≠ ⊤)
    (v : FourierLebesgueSpace L (-s) q) (u : FourierLebesgueSpace L s p) :
    sobolevDualEquiv s hp v u =
      WeightedCoeff.sobolevBilinearPairing s (sobolevCoefficients s p u)
        (sobolevCoefficients (-s) q v) := rfl

/-- The original coefficient norm equals the operator norm exactly. -/
theorem norm_sobolevDualEquiv (s : ℝ) (hp : p ≠ ⊤)
    (v : FourierLebesgueSpace L (-s) q) : ‖sobolevDualEquiv (p := p) s hp v‖ = ‖v‖ := by
  let K := WeightedCoeff.sobolevDualityIsometry (p := p) s hp
    (sobolevCoefficients (-s) q v)
  have hK : ‖K‖ = ‖v‖ := by simp only [K, LinearIsometryEquiv.norm_map]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro u
    change ‖K (sobolevCoefficients s p u)‖ ≤ ‖v‖ * ‖u‖
    simpa only [hK, LinearIsometryEquiv.norm_map] using
      K.le_opNorm (sobolevCoefficients s p u)
  · rw [← hK]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro a
    have h := (sobolevDualEquiv (p := p) s hp v).le_opNorm
      ((sobolevCoefficients s p).symm a)
    change ‖K (sobolevCoefficients s p ((sobolevCoefficients s p).symm a))‖ ≤
      ‖sobolevDualEquiv s hp v‖ * ‖(sobolevCoefficients s p).symm a‖ at h
    simpa only [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.norm_map] using h

/-- Section 2 duality on the original spaces at every real order and positive period. -/
def sobolevDualIsometry (s : ℝ) (hp : p ≠ ⊤) :
    FourierLebesgueSpace L (-s) q ≃ₗᵢ[ℂ] (FourierLebesgueSpace L s p →L[ℂ] ℂ) where
  toLinearEquiv := (sobolevDualEquiv s hp).toLinearEquiv
  norm_map' := norm_sobolevDualEquiv s hp

/-- The opposite Fourier index in the physical unconjugated pairing. -/
theorem sobolevDualIsometry_apply (s : ℝ) (hp : p ≠ ⊤)
    (v : FourierLebesgueSpace L (-s) q) (u : FourierLebesgueSpace L s p) :
    sobolevDualIsometry s hp v u = ∑' n : ℤ, u.val (mode (-n)) * v.val (mode n) := by
  change sobolevDualEquiv s hp v u = _
  rw [sobolevDualEquiv_apply, WeightedCoeff.sobolevBilinearPairing_apply]
  simp only [sobolevCoefficients_apply, neg_neg]

theorem sobolevDualIsometry_summable (s : ℝ)
    (v : FourierLebesgueSpace L (-s) q) (u : FourierLebesgueSpace L s p) :
    Summable (fun n : ℤ => ‖u.val (mode (-n)) * v.val (mode n)‖) := by
  simpa only [sobolevCoefficients_apply, neg_neg] using
    WeightedCoeff.summable_norm_sobolevBilinearPairing s
      (sobolevCoefficients s p u) (sobolevCoefficients (-s) q v)

/-- Every full functional has one actual distribution representative, with the exact norm. -/
theorem existsUnique_sobolevRepresentative (s : ℝ) (hp : p ≠ ⊤)
    (F : FourierLebesgueSpace L s p →L[ℂ] ℂ) :
    ∃! v : FourierLebesgueSpace L (-s) q,
      (∀ u : FourierLebesgueSpace L s p,
        F u = ∑' n : ℤ, u.val (mode (-n)) * v.val (mode n)) ∧ ‖v‖ = ‖F‖ := by
  refine ⟨(sobolevDualIsometry (q := q) s hp).symm F, ⟨?_, ?_⟩, ?_⟩
  · intro u
    simpa only [LinearIsometryEquiv.apply_symm_apply] using
      sobolevDualIsometry_apply s hp ((sobolevDualIsometry (q := q) s hp).symm F) u
  · exact LinearIsometryEquiv.norm_map _ _
  · intro v hv
    apply (sobolevDualIsometry s hp).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    ext u
    exact (sobolevDualIsometry_apply s hp v u).trans (hv.1 u).symm

/-- A smooth test as its normalized integral distribution, at every real order. -/
def ofSmooth (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SmoothPeriodicTest L) : FourierLebesgueSpace L s p :=
  ⟨Distribution.ofL1 f (f.smooth.continuous.intervalIntegrable 0 L), by
    obtain ⟨a, ha, _⟩ := existsUnique_smooth_arbitraryPeriod_coefficients (q := p)
      L Fact.out s f f.smooth f.periodic
    change Memℓp (fun n => (Weight.sobolev s n : ℂ) *
      Distribution.ofL1 f (f.smooth.continuous.intervalIntegrable 0 L) (mode (-n))) p
    have ha' : Memℓp (fun n => (Weight.sobolev s n : ℂ) * a.val n) p := a.property
    simpa only [Distribution.ofL1_coefficient, ← ha] using ha'⟩

@[simp] theorem ofSmooth_coefficient (s : ℝ) (f : SmoothPeriodicTest L) (n : ℤ) :
    (ofSmooth s p f).val (mode (-n)) = intervalFourierCoefficient L f n :=
  Distribution.ofL1_coefficient _ _ _

/-- The dual representative acts on smooth inputs by its original distributional action. -/
theorem sobolevDualIsometry_ofSmooth (s : ℝ) (hp : p ≠ ⊤)
    (v : FourierLebesgueSpace L (-s) q) (f : SmoothPeriodicTest L) :
    sobolevDualIsometry s hp v (ofSmooth s p f) = v.val f := by
  obtain ⟨b, hb, _⟩ := existsUnique_smooth_arbitraryPeriod_coefficients (q := p)
    L Fact.out (-(-s)) f f.smooth f.periodic
  have h := periodicDistribution_sobolevBilinearPairing_arbitraryPeriod L Fact.out (-s)
    v.val.toTempered v.val.toTempered_periodic (sobolevCoefficients (-s) q v)
    (fun n => (Distribution.toTempered_coefficient v.val n).symm)
    f f.smooth f.periodic b hb
  have haction : v.val.toTempered
      (SchwartzMap.smulLeftCLM ℂ f (periodCoefficientTest L Fact.out 0)) = v.val f :=
    congrArg (fun u : Distribution L => u f) (Distribution.ofTempered_toTempered v.val)
  rw [sobolevDualIsometry_apply]
  simp only [ofSmooth_coefficient]
  rw [WeightedCoeff.sobolevBilinearPairing_apply] at h
  simp only [sobolevCoefficients_apply, hb, haction] at h
  rw [← h]
  simpa only [Equiv.neg_apply, neg_neg, mul_comm] using
    (Equiv.neg ℤ).tsum_eq (fun n => v.val (mode (-n)) * intervalFourierCoefficient L f (-n))

/-- Smooth functions retain the source's factor 1/L and unconjugated integral. -/
theorem sobolevDualIsometry_ofSmooth_ofSmooth (s : ℝ) (hp : p ≠ ⊤)
    (f g : SmoothPeriodicTest L) :
    sobolevDualIsometry s hp (ofSmooth (-s) q g) (ofSmooth s p f) =
      (L : ℂ)⁻¹ * ∫ x in (0 : ℝ)..L, g x * f x := by
  rw [sobolevDualIsometry_ofSmooth]
  exact Distribution.ofL1_apply _ _ _

end NLS.Fourier.PeriodicFourierLebesgue
