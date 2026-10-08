import NLS.ZakharovShabat.SobolevEigenvectorRegularity
import NLS.ZakharovShabat.WeightedDomainPotential
import NLS.ZakharovShabat.PeriodicSpectrum

/-! # Original eigenvectors and linearly growing weighted domains

Weights comparable to one Fourier derivative have the same eigenvectors
as the original operator. Regularity, rather than a second contraction
hypothesis, supplies the inverse direction of the domain inclusion.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Forgetting the weight is injective in the base space. -/
theorem weightedBaseToPair_injective (w : SpectralWeight) :
    Function.Injective (weightedBaseToPair (p := p) w) := by
  intro a b h
  apply weightedPair_ext
  · intro k; simpa only [weightedBaseToPair_fst] using congrArg (fun v : PairSpace p => v.1 k) h
  · intro k; simpa only [weightedBaseToPair_snd] using congrArg (fun v : PairSpace p => v.2 k) h

/-- Forgetting the weight is injective on the derivative domain. -/
theorem weightedDomainToDomain_injective (w : SpectralWeight) :
    Function.Injective (weightedDomainToDomain (p := p) w) := by
  intro a b h
  apply weightedPair_ext
  · intro k; simpa only [weightedDomainToDomain_fst] using congrArg (fun v : Domain p => v.1.val k) h
  · intro k; simpa only [weightedDomainToDomain_snd] using congrArg (fun v : Domain p => v.2.val k) h

omit [Fact (1 ≤ p)] in
/-- Two ordinary derivatives suffice for a linearly growing weighted derivative domain. -/
theorem memlp_oneDerivative_of_sobolev_two (w : SpectralWeight) (C : ℝ)
    (hu : ∀ k : ℤ, w k ≤ C*(1+|(k:ℝ)|)) {f : ℤ → ℂ}
    (hf : Memℓp (fun k => (Weight.sobolev 2 k:ℂ)*f k) p) :
    Memℓp (fun k => (w.toWeight.oneDerivative k:ℂ)*f k) p := by
  apply (hf.norm.const_mul C).mono
  intro k
  simp only [Weight.oneDerivative_apply, Weight.sobolev_apply, Real.rpow_two,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (w.toWeight.positive k),
    abs_of_nonneg (by positivity : 0 ≤ 1+|(k:ℝ)|), abs_of_nonneg (sq_nonneg (1+|(k:ℝ)|))]
  have h := mul_le_mul_of_nonneg_right (hu k)
    (mul_nonneg (by positivity : 0 ≤ 1+|(k:ℝ)|) (norm_nonneg (f k)))
  simpa only [SpectralWeight.toWeight, mul_assoc, pow_two] using! h

/-- Every original eigenvector lifts to the weighted domain when the weight is comparable to H¹. -/
theorem exists_weightedDomain_of_eigenvector (hp : p ≠ ⊤) (w : SpectralWeight)
    (hl : ∀ k : ℤ, 1+|(k:ℝ)| ≤ w k) (C : ℝ)
    (hu : ∀ k : ℤ, w k ≤ C*(1+|(k:ℝ)|))
    (φ : WeightedCoeffPair w.toWeight p) (z : ℂ) (f : Domain p)
    (he : operator hp (weightedBaseToPair w φ) f = z • domainInclusion f) :
    ∃ g : WeightedDomain w.toWeight p, weightedDomainToDomain w g = f := by
  have hweight (k : ℤ) : Weight.sobolev 1 k ≤ w.toWeight k := by
    simpa only [Weight.sobolev_apply, Real.rpow_one] using hl k
  let a : Domain p := (WeightedCoeff.inclusionCLM _ _ hweight φ.fst,
    WeightedCoeff.inclusionCLM _ _ hweight φ.snd)
  have ha : domainInclusion a = weightedBaseToPair w φ := by
    apply Prod.ext <;> ext k <;>
      simp [a, domainInclusion_apply, scalarInclusion_apply, WeightedCoeff.inclusionCLM_apply]
  have hf := eigenvector_memlp_sobolev_two hp a f z (by simpa only [ha] using he)
  let g : WeightedDomain w.toWeight p := WithLp.toLp p
    ((⟨f.1.val, memlp_oneDerivative_of_sobolev_two w C hu hf.1⟩ : WeightedCoeff w.toWeight.oneDerivative p),
     (⟨f.2.val, memlp_oneDerivative_of_sobolev_two w C hu hf.2⟩ : WeightedCoeff w.toWeight.oneDerivative p))
  refine ⟨g, ?_⟩
  apply Prod.ext <;> apply Subtype.ext <;> funext k
  · exact weightedDomainToDomain_fst w g k
  · exact weightedDomainToDomain_snd w g k

/-- Original spectral points are exactly weighted eigenvectors for linearly growing weights. -/
theorem mem_periodicSpectrum_iff_linearWeight_eigenvector (hp : p ≠ ⊤) (w : SpectralWeight)
    (hl : ∀ k : ℤ, 1+|(k:ℝ)| ≤ w k) (C : ℝ)
    (hu : ∀ k : ℤ, w k ≤ C*(1+|(k:ℝ)|))
    (φ : WeightedCoeffPair w.toWeight p) (z : ℂ) :
    z ∈ periodicSpectrum hp (weightedBaseToPair w φ) ↔
      ∃ f : WeightedDomain w.toWeight p, f ≠ 0 ∧
        weightedFreePencil w.toWeight z f = weightedDomainPotential hp w φ f := by
  rw [mem_periodicSpectrum_iff_exists_eigenvector]
  constructor
  · rintro ⟨f,hf,he⟩
    obtain ⟨g,hg⟩ := exists_weightedDomain_of_eigenvector hp w hl C hu φ z f he
    refine ⟨g, ?_, ?_⟩
    · intro hzero
      apply hf
      rw [← hg, hzero, map_zero]
    · apply weightedBaseToPair_injective w
      rw [weightedFreePencil_eq_original, weightedDomainPotential_eq_original, hg]
      have h : freeOperator f + potentialOperator hp (weightedBaseToPair w φ) f = z • domainInclusion f := he
      rw [sub_eq_iff_eq_add]
      exact h.symm.trans (add_comm _ _)
  · rintro ⟨f,hf,he⟩
    refine ⟨weightedDomainToDomain w f, ?_, ?_⟩
    · intro hzero
      apply hf
      apply weightedDomainToDomain_injective w
      simpa only [map_zero] using hzero
    · have h := congrArg (weightedBaseToPair w) he
      rw [weightedFreePencil_eq_original, weightedDomainPotential_eq_original] at h
      change freeOperator _ + potentialOperator hp (weightedBaseToPair w φ) _ = _
      exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp h).symm

end NLS.ZakharovShabat
