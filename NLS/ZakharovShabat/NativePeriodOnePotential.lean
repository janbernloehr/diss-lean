import NLS.Fourier.PeriodicFourierLebesguePeriodDoubling
import NLS.ZakharovShabat.NativePeriodicOperator
import NLS.ZakharovShabat.PeriodOneEmbedding

/-! # Original period-one distribution potentials in the native periodic operator

Both components retain exactly the same physical tempered distribution when
regarded as period-two potentials. The finite component-sum norm is preserved,
and the resulting spectrum is the established spectrum of the period-one
source parameter, including for nonmeasure Fourier–Lebesgue distributions.
-/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.ZakharovShabat.NativePeriodic
open NLS.Fourier SmoothPeriodicTest PeriodicFourierLebesgue

/-- Original period-one potential pairs, with the finite component-sum norm. -/
abbrev SourceSpace (p : ℝ≥0∞) := WithLp p
  (PeriodicFourierLebesgue 1 Weight.one p × PeriodicFourierLebesgue 1 Weight.one p)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The exact normalized Fourier coefficients of the original source pair. -/
def sourceCoefficients (p : ℝ≥0∞) [Fact (1 ≤ p)] : SourceSpace p ≃ₗᵢ[ℂ] CoeffPair p :=
  (unweightedCoefficients p).withLpProdCongr p (unweightedCoefficients p)

/-- Regard the original distribution potential as period two, without changing it physically. -/
def extendPotential : SourceSpace p →ₗᵢ[ℂ] Space p :=
  PeriodicFourierLebesgue.periodDouble.withLpProdMap p PeriodicFourierLebesgue.periodDouble

theorem extendPotential_fst_toTempered (φ : SourceSpace p) :
    (extendPotential φ).fst.val.toTempered = φ.fst.val.toTempered :=
  periodDouble_toTempered φ.fst

theorem extendPotential_snd_toTempered (φ : SourceSpace p) :
    (extendPotential φ).snd.val.toTempered = φ.snd.val.toTempered :=
  periodDouble_toTempered φ.snd

/-- The full original finite source norm is unchanged by the period extension. -/
theorem norm_extendPotential (φ : SourceSpace p) : ‖extendPotential φ‖ = ‖φ‖ :=
  extendPotential.norm_map φ

/-- Every coefficient agrees with the period-one parameter used throughout the spectral theory. -/
@[simp] theorem coefficients_extendPotential (φ : SourceSpace p) :
    coefficients p (extendPotential φ) = periodOnePair (sourceCoefficients p φ) := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext
  · exact unweightedCoefficients_periodDouble φ.fst
  · exact unweightedCoefficients_periodDouble φ.snd

/-- The entire image consists of exactly the period-one physical distribution pairs. -/
theorem mem_range_extendPotential_iff (φ : Space p) :
    φ ∈ extendPotential.toLinearMap.range ↔
      IsPeriodicDistribution 1 φ.fst.val.toTempered ∧
        IsPeriodicDistribution 1 φ.snd.val.toTempered := by
  constructor
  · rintro ⟨u, rfl⟩
    change IsPeriodicDistribution 1 (extendPotential u).fst.val.toTempered ∧
      IsPeriodicDistribution 1 (extendPotential u).snd.val.toTempered
    rw [extendPotential_fst_toTempered, extendPotential_snd_toTempered]
    exact ⟨u.fst.val.toTempered_periodic, u.snd.val.toTempered_periodic⟩
  · rintro ⟨h₁, h₂⟩
    obtain ⟨u, hu⟩ := (mem_range_periodDouble_iff φ.fst).mpr h₁
    obtain ⟨v, hv⟩ := (mem_range_periodDouble_iff φ.snd).mpr h₂
    refine ⟨WithLp.toLp p (u,v), ?_⟩
    apply (WithLp.prodContinuousLinearEquiv p ℂ _ _).injective
    exact Prod.ext hu hv

/-- The native spectrum at the extended original source is exactly the existing source spectrum. -/
theorem spectrum_extendPotential (hp : p ≠ ⊤) (φ : SourceSpace p) :
    spectrum hp (extendPotential φ) = periodicSpectrum hp (periodOnePotential (sourceCoefficients p φ)) := by
  rw [spectrum_eq, coefficients_extendPotential]
  rfl

end NLS.ZakharovShabat.NativePeriodic
