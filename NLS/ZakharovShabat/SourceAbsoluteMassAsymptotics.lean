import NLS.ZakharovShabat.ClassicalDiscriminantMassAsymptotics
import NLS.ZakharovShabat.SourceHilbertMass
import NLS.ZakharovShabat.HilbertDiscriminant
import NLS.ZakharovShabat.PeriodOneEmbedding
import NLS.Fourier.PeriodOneCoefficients
import NLS.Fourier.IntervalBilinearParseval
import NLS.Fourier.IntervalL2Realization

/-! # Physical mass recovery for absolutely summable sources

Actual period-one Fourier synthesis provides a continuous representative.
Bilinear Parseval identifies its physical mass with the original reflected
source pairing, and the canonical/classical trace identity transports the
first discriminant coefficient without changing its normalization.
-/
noncomputable section
open Set Complex MeasureTheory Filter Topology
open NLS.Fourier NLS.LinearVolterra NLS.Poisson
namespace NLS.ZakharovShabat

/-- Restrict the two absolutely convergent period-one Fourier series. -/
def absoluteSourceCurve (a b : Coeff 1) : Curve (ℂ × ℂ) :=
  ⟨fun t => (periodOneSynthesis a t, periodOneSynthesis b t),
    ((continuous_periodOneSynthesis a).prodMk (continuous_periodOneSynthesis b)).comp
      continuous_subtype_val⟩

@[simp] theorem extend_absoluteSourceCurve (a b : Coeff 1) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    extend (absoluteSourceCurve a b) t = (periodOneSynthesis a t, periodOneSynthesis b t) :=
  extend_coe (absoluteSourceCurve a b) ⟨t,ht⟩

private theorem circlePullback_periodOneSynthesis_of_coefficients
    (a : Coeff 1) (b : Coeff 2) (hab : ∀ n : ℤ, a n = b n) :
    circlePullback (l2Synthesis (Coeff.periodDouble b))
      =ᵐ[volume.restrict (Ioc 0 2)] periodOneSynthesis a := by
  have hm := memLp_two_interval (continuous_periodOneSynthesis a) 0 2 (by norm_num)
  have he : periodTwoL2Coefficients (periodOneSynthesis a) hm = Coeff.periodDouble b := by
    ext n
    rw [periodTwoL2Coefficients_apply, periodTwoCoefficient_periodOneSynthesis]
    by_cases hn : n % 2 = 0
    · have hn' : n = 2*(n/2) := by omega
      rw [hn', Coeff.periodDouble_even, Coeff.periodDouble_even, hab]
    · have hn' : n = 2*(n/2)+1 := by omega
      rw [hn', Coeff.periodDouble_odd, Coeff.periodDouble_odd]
  simpa only [he] using circlePullback_periodTwoL2Coefficients (periodOneSynthesis a) hm

/-- Absolute Fourier synthesis represents the original source on the physical interval. -/
theorem physicalBase_absoluteSourceCurve (φ : CoeffPair 2) (a b : Coeff 1)
    (ha : ∀ n : ℤ, a n = φ.fst n) (hb : ∀ n : ℤ, b n = φ.snd n) :
    physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)]
      extend (absoluteSourceCurve a b) := by
  have h₁ := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2))
    (circlePullback_periodOneSynthesis_of_coefficients a φ.fst ha)
  have h₂ := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2))
    (circlePullback_periodOneSynthesis_of_coefficients b φ.snd hb)
  filter_upwards [h₁,h₂,ae_restrict_mem measurableSet_Ioc] with t ht₁ ht₂ ht
  rw [extend_absoluteSourceCurve a b t (Ioc_subset_Icc_self ht)]
  exact Prod.ext ht₁ ht₂

/-- The physical integral equals the original source mass by bilinear Parseval.
This statement includes complex sources and keeps the frequency reversal explicit. -/
theorem classicalPhysicalMass_absoluteSourceCurve (φ : CoeffPair 2) (a b : Coeff 1)
    (ha : ∀ n : ℤ, a n = φ.fst n) (hb : ∀ n : ℤ, b n = φ.snd n) :
    classicalPhysicalMass (absoluteSourceCurve a b) = sourceHilbertMass φ := by
  have he : classicalPhysicalMass (absoluteSourceCurve a b) =
      ∫ t in (0 : ℝ)..1, periodOneSynthesis a t * periodOneSynthesis b t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    dsimp only
    rw [extend_absoluteSourceCurve a b t ht']
  rw [he, ← tsum_bilinear_unitFourierCoefficient
    (continuous_periodOneSynthesis a) (continuous_periodOneSynthesis b)]
  have hc (c : Coeff 1) (n : ℤ) : unitFourierCoefficient (periodOneSynthesis c) n = c n := by
    rw [unitFourierCoefficient_eq_fourierCoeffOn]
    exact periodOneCoefficient_synthesis c n
  simp only [hc, ha, hb]
  rw [sourceHilbertMass, reflectedHilbertPairing_apply,
    ← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => φ.fst n * φ.snd (-n))]
  simp only [Equiv.neg_apply, neg_neg]

/-- Every absolutely summable Hilbert source has the canonical high-energy
mass coefficient, with no real-type or spectral hypothesis. -/
theorem tendsto_sourceDiscriminant_mass_coefficient_of_absolute
    (φ : CoeffPair 2) (ha : Memℓp (fun n : ℤ => φ.fst n) 1)
    (hb : Memℓp (fun n : ℤ => φ.snd n) 1) :
    Tendsto (fun y : ℝ => (2*y : ℂ) *
      (exp (-(y : ℂ)) * canonicalDiscriminant (by simp) (periodOnePotential φ) ((y : ℂ)*I) - 1))
      atTop (𝓝 (sourceHilbertMass φ)) := by
  let a : Coeff 1 := ⟨_,ha⟩
  let b : Coeff 1 := ⟨_,hb⟩
  have hc := tendsto_classicalDiscriminant_mass_coefficient (absoluteSourceCurve a b)
  rw [classicalPhysicalMass_absoluteSourceCurve φ a b (fun _ => rfl) (fun _ => rfl)] at hc
  have he : canonicalDiscriminant (by simp) (periodOnePotential φ) =
      classicalDiscriminant (absoluteSourceCurve a b) := by
    funext z
    exact canonicalDiscriminant_eq_classical _ (periodOnePotential_mem _) _
      (physicalBase_absoluteSourceCurve φ a b (fun _ => rfl) (fun _ => rfl)) z
  rw [he]
  exact hc

/-- Equality of canonical discriminants preserves the original mass for
absolutely summable Hilbert sources. -/
theorem sourceHilbertMass_eq_of_discriminant_eq_of_absolute
    (φ ψ : CoeffPair 2)
    (hφ₁ : Memℓp (fun n : ℤ => φ.fst n) 1) (hφ₂ : Memℓp (fun n : ℤ => φ.snd n) 1)
    (hψ₁ : Memℓp (fun n : ℤ => ψ.fst n) 1) (hψ₂ : Memℓp (fun n : ℤ => ψ.snd n) 1)
    (heq : canonicalDiscriminant (by simp) (periodOnePotential φ) =
      canonicalDiscriminant (by simp) (periodOnePotential ψ)) :
    sourceHilbertMass φ = sourceHilbertMass ψ := by
  have hφ := tendsto_sourceDiscriminant_mass_coefficient_of_absolute φ hφ₁ hφ₂
  rw [heq] at hφ
  exact tendsto_nhds_unique hφ (tendsto_sourceDiscriminant_mass_coefficient_of_absolute ψ hψ₁ hψ₂)

end NLS.ZakharovShabat
