import NLS.ZakharovShabat.SourceFiniteGapExteriorMass
import NLS.ZakharovShabat.SourceCanonicalRootExponent
import NLS.ZakharovShabat.SourceAntiDiscriminantIdentity
import NLS.ZakharovShabat.SourceBoundaryExponentDifferential

/-! # Exponent-independent mass of finite-gap sources

The coefficient pairing is absolutely summable at every finite-gap source.
Exponent compatibility transfers the Hilbert mass remainder to the original
source, including the filled values of the Floquet logarithmic derivative.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

theorem sourceFloquetLogDerivative_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (φ : CoeffPair p) :
    sourceFloquetLogDerivative hp hp1 φ =
      sourceFloquetLogDerivative hq hq1 (CoeffPair.exponentInclusion hpq φ) := by
  have he : sourceFloquetMultiplier hp hp1 φ =
      sourceFloquetMultiplier hq hq1 (CoeffPair.exponentInclusion hpq φ) := by
    funext z
    simp only [sourceFloquetMultiplier,sourceDiscriminant_exponent hp hq hpq φ,
      sourceCanonicalRoot_exponent hp hq hp1 hq1 hpq φ]
  unfold sourceFloquetLogDerivative
  rw [he]

theorem sourceFiniteGapLocus_exponent_iff
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (φ : realTypeSourceSubmodule p) :
    φ ∈ sourceFiniteGapLocus hp hp1 ↔
      realTypeSourceExponentInclusion hpq φ ∈ sourceFiniteGapLocus hq hq1 := by
  change {j : ℤ | canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) j ≠ 0}.Finite ↔
    {j : ℤ | canonicalPeriodicGap hq hq1 (periodOnePotential (CoeffPair.exponentInclusion hpq φ.val))
      (periodOnePotential_mem _) j ≠ 0}.Finite
  simp only [canonicalPeriodicGap,
    (canonicalPeriodicEndpoints_periodOne_exponent hp hq hp1 hq1 hpq φ.val).1,
    (canonicalPeriodicEndpoints_periodOne_exponent hp hq hp1 hq1 hpq φ.val).2]

/-- A finite-gap source at any finite exponent has the same Fourier
coefficients and filled logarithmic derivative as a finite-gap Hilbert source. -/
theorem sourceFiniteGap_exists_hilbert_mass_model
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ ψ : realTypeSourceSubmodule 2,
      (∀ k : ℤ, ψ.val.fst k = φ.val.fst k ∧ ψ.val.snd k = φ.val.snd k) ∧
      ψ ∈ sourceFiniteGapLocus (by simp) (by norm_num) ∧
      sourceFloquetLogDerivative hp hp1 φ.val = sourceFloquetLogDerivative (by simp) (by norm_num) ψ.val := by
  rcases le_total p 2 with hp2 | h2p
  · let ψ := realTypeSourceExponentInclusion hp2 φ
    refine ⟨ψ,fun _ => ⟨rfl,rfl⟩,?_,?_⟩
    · exact (sourceFiniteGapLocus_exponent_iff hp (by simp) hp1 (by norm_num) hp2 φ).mp hf
    · exact sourceFloquetLogDerivative_exponent hp (by simp) hp1 (by norm_num) hp2 φ.val
  · obtain ⟨u,hu,hru,_⟩ := sourceFiniteGap_exists_hilbert_realization hp hp1 h2p φ hf
    let ψ : realTypeSourceSubmodule 2 := ⟨u,hru⟩
    have he : realTypeSourceExponentInclusion h2p ψ = φ := Subtype.ext hu
    refine ⟨ψ,?_,?_,?_⟩
    · intro k
      exact ⟨congrArg (fun v : CoeffPair p => v.fst k) hu,
        congrArg (fun v : CoeffPair p => v.snd k) hu⟩
    · apply (sourceFiniteGapLocus_exponent_iff (by simp) hp (by norm_num) hp1 h2p ψ).mpr
      simpa only [he] using! hf
    · simpa only [hu] using (sourceFloquetLogDerivative_exponent (by simp) hp (by norm_num) hp1 h2p u).symm

/-- The physical mass pairing is absolutely convergent at every real finite-gap source. -/
theorem summable_norm_sourceFiniteGap_mass
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    Summable (fun k : ℤ => ‖φ.val.fst k*φ.val.snd (-k)‖) := by
  obtain ⟨ψ,hcoeff,_,_⟩ := sourceFiniteGap_exists_hilbert_mass_model hp hp1 φ hf
  simpa only [(hcoeff _).1,(hcoeff _).2] using NLS.Poisson.summable_norm_reflectedHilbertPairing ψ.val.fst ψ.val.snd

/-- The exterior derivative coefficient is the original Fourier mass pairing,
independently of the ambient source exponent. -/
theorem exists_sourceFiniteGap_coefficient_mass_remainder
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ r : ℝ, 0 < r ∧ ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (ball 0 r) ∧
      h 0 = -I*(∑' k : ℤ, φ.val.fst k*φ.val.snd (-k))/2 ∧
      ∀ z : ℂ, r⁻¹ < ‖z‖ → sourceFloquetLogDerivative hp hp1 φ.val z = -I+z⁻¹^2*h z⁻¹ := by
  obtain ⟨ψ,hcoeff,hfψ,he⟩ := sourceFiniteGap_exists_hilbert_mass_model hp hp1 φ hf
  obtain ⟨r,hr,h,hh,hh0,hd,_⟩ := exists_sourceFiniteGap_mass_remainder ψ hfψ
  refine ⟨r,hr,h,hh,?_,?_⟩
  · simpa only [sourceHilbertMass,NLS.Poisson.reflectedHilbertPairing_apply,
      (hcoeff _).1,(hcoeff _).2] using hh0
  · simpa only [he] using hd

end NLS.ZakharovShabat
