import NLS.ZakharovShabat.PeriodicSpectralDataUniqueness
import NLS.ZakharovShabat.PeriodicEndpointProducts
import NLS.ZakharovShabat.CanonicalPeriodicLevels
import Mathlib.Analysis.Analytic.Uniqueness

/-! # The normalized discriminant and intrinsic periodic spectral data

For real-type even potentials, the original periodic spectrum and its
algebraic multiplicities determine the discriminant. The endpoint product
first determines its square; the known value at the zero-index endpoint
fixes the sign, and analytic uniqueness extends equality globally.
Conversely, the discriminant recovers the original spectrum and every
algebraic multiplicity through the full periodic product.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The normalized discriminant is an invariant of the full original
periodic spectral data at real-type even potentials. -/
theorem canonicalDiscriminant_eq_of_spectral_data (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (hψ : ψ ∈ pairParitySubspace 0)
    (hrealφ : IsRealType φ) (hrealψ : IsRealType ψ)
    (hspec : periodicSpectrum hp φ = periodicSpectrum hp ψ)
    (hmult : ∀ z, periodicAlgebraicMultiplicity hp φ z = periodicAlgebraicMultiplicity hp ψ z) :
    canonicalDiscriminant hp φ = canonicalDiscriminant hp ψ := by
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1 φ ψ hφ hψ hspec hmult
  have hprod : canonicalPeriodicProduct hp φ = canonicalPeriodicProduct hp ψ := by
    rw [← canonicalPeriodicEndpoints_product hp hp1 φ hφ,
      ← canonicalPeriodicEndpoints_product hp hp1 ψ hψ,hl,hr]
  have hsq (z : ℂ) : (canonicalDiscriminant hp φ z)^2 = (canonicalDiscriminant hp ψ z)^2 := by
    have he := congrFun hprod z
    rw [canonicalPeriodic_eq_discriminant_sq_sub_four_finite hp hp1 φ hφ,
      canonicalPeriodic_eq_discriminant_sq_sub_four_finite hp hp1 ψ hψ] at he
    linear_combination he
  let z₀ := canonicalPeriodicLeft hp hp1 φ hφ 0
  have h₀φ : canonicalDiscriminant hp φ z₀ = 2 := by
    simpa only [Int.zero_emod,ite_true] using
      (canonicalPeriodicEndpoints_discriminant_of_realType hp hp1 φ hφ hrealφ 0).1
  have h₀ψ : canonicalDiscriminant hp ψ z₀ = 2 := by
    dsimp only [z₀]
    rw [hl]
    simpa only [Int.zero_emod,ite_true] using
      (canonicalPeriodicEndpoints_discriminant_of_realType hp hp1 ψ hψ hrealψ 0).1
  have ha := analyticOnNhd_canonicalDiscriminant hp hp1 φ hφ
  have hb := analyticOnNhd_canonicalDiscriminant hp hp1 ψ hψ
  have hne : ∀ᶠ z in 𝓝 z₀, canonicalDiscriminant hp φ z+canonicalDiscriminant hp ψ z ≠ 0 :=
    ((ha z₀ (mem_univ _)).continuousAt.add (hb z₀ (mem_univ _)).continuousAt).eventually_ne
      (by
        change canonicalDiscriminant hp φ z₀+canonicalDiscriminant hp ψ z₀ ≠ 0
        rw [h₀φ,h₀ψ]
        norm_num)
  apply ha.eq_of_eventuallyEq hb
  filter_upwards [hne] with z hz
  apply sub_eq_zero.mp
  have he : (canonicalDiscriminant hp φ z-canonicalDiscriminant hp ψ z)*
      (canonicalDiscriminant hp φ z+canonicalDiscriminant hp ψ z) = 0 := by
    calc
      _ = (canonicalDiscriminant hp φ z)^2-(canonicalDiscriminant hp ψ z)^2 := by ring
      _ = 0 := by rw [hsq,sub_self]
  exact (mul_eq_zero.mp he).resolve_right hz

/-- Equality of discriminants recovers both the operator spectrum and
its actual algebraic multiplicity at every spectral parameter. -/
theorem periodic_spectral_data_eq_of_discriminant_eq (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (hψ : ψ ∈ pairParitySubspace 0)
    (h : canonicalDiscriminant hp φ = canonicalDiscriminant hp ψ) :
    periodicSpectrum hp φ = periodicSpectrum hp ψ ∧
      ∀ z, periodicAlgebraicMultiplicity hp φ z = periodicAlgebraicMultiplicity hp ψ z := by
  have hprod : canonicalPeriodicProduct hp φ = canonicalPeriodicProduct hp ψ := by
    funext z
    rw [canonicalPeriodic_eq_discriminant_sq_sub_four_finite hp hp1 φ hφ,
      canonicalPeriodic_eq_discriminant_sq_sub_four_finite hp hp1 ψ hψ,h]
  constructor
  · ext z
    rw [← canonicalPeriodicProduct_eq_zero_iff hp hp1 φ,
      ← canonicalPeriodicProduct_eq_zero_iff hp hp1 ψ,hprod]
  · intro z
    have he := congrArg (fun f : ℂ → ℂ => analyticOrderAt f z) hprod
    rw [analyticOrderAt_canonicalPeriodicProduct hp hp1 φ,
      analyticOrderAt_canonicalPeriodicProduct hp hp1 ψ] at he
    exact_mod_cast he

end NLS.ZakharovShabat
