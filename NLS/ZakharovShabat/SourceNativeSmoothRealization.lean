import NLS.Fourier.ArbitraryPeriodDistributionPairing
import NLS.Fourier.ArbitraryPeriodBilinearParseval
import NLS.ZakharovShabat.SourceNativeSobolevPhysicalJets

/-! # Smooth physical fields in every original native Sobolev source

The construction uses the actual unit-period Fourier integrals. Every real
physical conjugate pair has a native representative at each integer order;
its bounded lower jets recover the original smooth physical derivatives.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Fourier
open scoped ContDiff ComplexConjugate
namespace NLS.ZakharovShabat

theorem periodOneCoefficient_eq_interval (f : ℝ → ℂ) (n : ℤ) :
    periodOneCoefficient f n = intervalFourierCoefficient 1 f n := by
  simpa only [periodOneCoefficient] using
    (intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num : (0:ℝ) < 1) f n).symm

/-- Every smooth period-one physical conjugate pair has an original native
real Sobolev source with exactly its actual Fourier coefficients. -/
theorem exists_nativeSobolevSource_of_smooth (s : ℕ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1)
    (hr : ∀ x, g x = conj (f x)) :
    ∃ a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight s (Nat.cast_nonneg s)),
      ∀ n : ℤ, (originalWeightedRealSource _ a).val.fst n = periodOneCoefficient f n ∧
        (originalWeightedRealSource _ a).val.snd n = periodOneCoefficient g n := by
  obtain ⟨a,ha,_⟩ := existsUnique_smooth_arbitraryPeriod_coefficients (q := 2) 1 (by norm_num) s f hf hpf
  obtain ⟨b,hb,_⟩ := existsUnique_smooth_arbitraryPeriod_coefficients (q := 2) 1 (by norm_num) s g hg hpg
  let w := sourceSobolevSpectralWeight s (Nat.cast_nonneg s)
  let L := WeightedCoeff.inclusionCLM (p := 2) (Weight.sobolev s) (sourceFrequencyWeight w)
    (by intro n; simp [w])
  let q : WeightedCoeffPair (sourceFrequencyWeight w) 2 := WithLp.toLp 2 (L a,L b)
  have hq : q ∈ weightedRealSourceSubmodule w := by
    rw [mem_weightedRealSourceSubmodule_iff]
    intro n
    change (L b).val n = conj ((L a).val (-n))
    rw [WeightedCoeff.inclusionCLM_apply,WeightedCoeff.inclusionCLM_apply,hb,ha]
    have he : g = fun x => conj (f x) := funext hr
    rw [he,intervalFourierCoefficient_conj]
  refine ⟨⟨q,hq⟩,?_⟩
  intro n
  constructor
  · rw [originalWeightedRealSource_fst,periodOneCoefficient_eq_interval]
    change (L a).val n = _
    rw [WeightedCoeff.inclusionCLM_apply,ha]
  · rw [originalWeightedRealSource_snd,periodOneCoefficient_eq_interval]
    change (L b).val n = _
    rw [WeightedCoeff.inclusionCLM_apply,hb]

/-- Native lower jets of any represented smooth fields are exactly their
classical physical derivatives; no spectral support condition is needed. -/
theorem nativeSobolevPhysicalJet_eq_smooth (s k : ℕ) (hk : k < s)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight s (Nat.cast_nonneg s)))
    (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1)
    (ha : ∀ n : ℤ, (originalWeightedRealSource _ a).val.fst n = periodOneCoefficient f n ∧
      (originalWeightedRealSource _ a).val.snd n = periodOneCoefficient g n) :
    (fun x : ℝ => (nativeSobolevPhysicalJetCLM s k hk a).1 (x : AddCircle (2:ℝ))) = iteratedDeriv k f ∧
    (fun x : ℝ => (nativeSobolevPhysicalJetCLM s k hk a).2 (x : AddCircle (2:ℝ))) = iteratedDeriv k g := by
  constructor
  · apply hierarchySobolevJetContinuous_eq_classical s k hk _ _ hf hpf
    intro n
    change (originalSobolevToHigher s a.val).1.val n = _
    rw [originalSobolevToHigher_fst]
    simpa only [originalWeightedRealSource_fst] using (ha n).1
  · apply hierarchySobolevJetContinuous_eq_classical s k hk _ _ hg hpg
    intro n
    change (originalSobolevToHigher s a.val).2.val n = _
    rw [originalSobolevToHigher_snd]
    simpa only [originalWeightedRealSource_snd] using (ha n).2

/-- Every smooth real period-one scalar field has an actual equal-field
native source at every integer regularity. -/
theorem exists_nativeSobolevSource_of_smooth_real (s : ℕ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) (hr : ∀ x, (f x).im = 0) :
    ∃ a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight s (Nat.cast_nonneg s)),
      (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd ∧
      ∀ n : ℤ, (originalWeightedRealSource _ a).val.fst n = periodOneCoefficient f n ∧
        (originalWeightedRealSource _ a).val.snd n = periodOneCoefficient f n := by
  have hc (x : ℝ) : f x = conj (f x) := by
    apply Complex.ext <;> simp [hr x]
  obtain ⟨a,ha⟩ := exists_nativeSobolevSource_of_smooth s f f hf hf hp hp hc
  refine ⟨a,?_,ha⟩
  ext n
  exact (ha n).1.trans (ha n).2.symm

end NLS.ZakharovShabat
