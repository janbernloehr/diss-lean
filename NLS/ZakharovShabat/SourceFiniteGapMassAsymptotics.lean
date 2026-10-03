import NLS.ZakharovShabat.SourceAbsoluteMassAsymptotics
import NLS.ZakharovShabat.SourceFiniteGapHilbertRealization
import NLS.ZakharovShabat.SourceRealTypeBanachSpace

/-! # The mass coefficient at actual finite-gap Hilbert sources

The existing Sobolev bootstrap discharges absolute coefficient summability.
Thus the canonical source discriminant recovers the original mass and the
half-square Hilbert norm, with no physical representative left as a premise.
-/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Finite spectral support implies absolute summability of both original
source Fourier series, even when their Fourier support is infinite. -/
theorem sourceFiniteGap_memlp_one {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    Memℓp (fun n : ℤ => φ.val.fst n) 1 ∧ Memℓp (fun n : ℤ => φ.val.snd n) 1 := by
  have h := sourceFiniteGap_mem_H1 hp hp1 φ hfinite
  have hembed (a : Coeff p)
      (ha : Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*a n) 2) :
      Memℓp (fun n : ℤ => a n) 1 := by
    let b : ScalarDomain 2 := ⟨_,ha⟩
    have hb := (WeightedCoeff.sobolevToL1CLM 2 (by simp) b).property
    change Memℓp (fun n => WeightedCoeff.sobolevToL1CLM 2 (by simp) b n) 1 at hb
    simpa only [WeightedCoeff.sobolevToL1CLM_apply] using hb
  exact ⟨hembed _ h.1, hembed _ h.2⟩

/-- The first canonical discriminant coefficient is the actual Hilbert
source mass at every real finite-gap source. -/
theorem tendsto_sourceDiscriminant_mass_coefficient_finiteGap
    (φ : realTypeSourceSubmodule 2)
    (hfinite : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    Tendsto (fun y : ℝ => (2*y : ℂ) *
      (exp (-(y : ℂ)) * canonicalDiscriminant (by simp) (periodOnePotential φ.val) ((y : ℂ)*I) - 1))
      atTop (𝓝 (sourceHilbertMass φ.val)) := by
  have h := sourceFiniteGap_memlp_one (by simp) (by norm_num) φ hfinite
  exact tendsto_sourceDiscriminant_mass_coefficient_of_absolute φ.val h.1 h.2

/-- In the dissertation's original real source normalization, the coefficient
is half the square of the source norm. -/
theorem tendsto_sourceDiscriminant_norm_coefficient_finiteGap
    (φ : realTypeSourceSubmodule 2)
    (hfinite : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    Tendsto (fun y : ℝ => (2*y : ℂ) *
      (exp (-(y : ℂ)) * canonicalDiscriminant (by simp) (periodOnePotential φ.val) ((y : ℂ)*I) - 1))
      atTop (𝓝 ((‖φ.val‖^2/2 : ℝ) : ℂ)) := by
  simpa only [sourceHilbertMass_eq_half_norm_sq_of_realType φ.val φ.property] using
    tendsto_sourceDiscriminant_mass_coefficient_finiteGap φ hfinite

/-- Isospectral finite-gap real sources have the same original Hilbert norm. -/
theorem norm_eq_of_sourceDiscriminant_eq_finiteGap
    (φ ψ : realTypeSourceSubmodule 2)
    (hφ : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (hψ : ψ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (heq : canonicalDiscriminant (by simp) (periodOnePotential φ.val) =
      canonicalDiscriminant (by simp) (periodOnePotential ψ.val)) :
    ‖φ.val‖ = ‖ψ.val‖ := by
  have ha := sourceFiniteGap_memlp_one (by simp) (by norm_num) φ hφ
  have hb := sourceFiniteGap_memlp_one (by simp) (by norm_num) ψ hψ
  have hm := sourceHilbertMass_eq_of_discriminant_eq_of_absolute φ.val ψ.val ha.1 ha.2 hb.1 hb.2 heq
  rw [sourceHilbertMass_eq_half_norm_sq_of_realType φ.val φ.property,
    sourceHilbertMass_eq_half_norm_sq_of_realType ψ.val ψ.property] at hm
  have hr := Complex.ofReal_injective hm
  nlinarith [norm_nonneg φ.val, norm_nonneg ψ.val]

end NLS.ZakharovShabat
