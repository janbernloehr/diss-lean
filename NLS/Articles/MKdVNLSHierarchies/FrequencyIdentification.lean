import NLS.MKdV.MiuraEvenFrequencySharpExtension
import NLS.Articles.MKdVNLSHierarchies.FrequencyMassEndpoint

/-! # Corrected Theorem 3 at every order on the full original real domain

The restricted original NLS frequency is characterized by the actual
original S_(2m) angle bracket and unique continuous continuation to
H^(m-1). It equals the raw positive-action derivative of every independent
physical K_m normal form, including every closed selected action. The
printed (-1)^m factor has the previously checked zero-profile refutation.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

/-- The actual original angle bracket uniquely specifies the restricted
NLS frequency on ALL real H^(m-1) profiles, at every positive order. -/
theorem theorem3_original_frequency_extension_certificate (m : ℕ) (_hm : 1 ≤ m)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃! f : MiuraRealSobolevSource (m-1) → ℂ, IsMiuraOriginalEvenFrequencyExtension (m-1) n f :=
  existsUnique_miuraOriginalEvenFrequencyExtension (m-1) n hn

/-- The defining frequency agrees with the actual original S_(2s+2)
differential on its full H^(s+1) open-angle domain, not with a prescribed
Hill-side value. Its vector has exactly the original NLS Hamiltonian coefficients. -/
theorem theorem3_original_bracket_agreement (s : ℕ) (n : ℕ) (hn : 1 ≤ n)
    (a : MiuraRealSobolevSource (s+1))
    (hgap : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (miuraSobolevActionSource (s+1) a.val)) (periodOnePotential_mem _) n ≠ 0) :
    miuraOriginalEvenNLSFrequency s n hn (miuraRealSobolevLower s a) =
      -fderiv ℂ (sobolevEvenHamiltonian (s+1) (by omega)) (a.val,a.val)
        (miuraHigherSobolevThetaVector (s+1) a n hgap) ∧
      higherSobolevSourceInclusion (s+1) (miuraHigherSobolevThetaVector (s+1) a n hgap) =
        sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n miuraNLSAngleFamily.psi
          (miuraSobolevActionSource (s+1) a.val) :=
  ⟨(miuraOriginalEvenNLSFrequency_spec s n hn).2 a hgap,
    miuraHigherSobolevThetaVector_inclusion (s+1) a n hgap⟩

/-- Corrected Theorem 3, with the physical positive sign: the actual
restricted NLS frequency equals the independent K_m action derivative
on EVERY real H^(m-1) profile. No open-gap or extra-regularity premise remains. -/
theorem theorem3_corrected (m : ℕ) (_hm : 1 ≤ m) (n : ℕ) (hn : 1 ≤ n)
    (D : MiuraNativeHamiltonianActionData (m-1)) (a : MiuraRealSobolevSource (m-1)) :
    miuraOriginalEvenNLSFrequency (m-1) n hn a =
      D.frequency (n : ℤ) (miuraNativeActionMeanMap (m-1) a.val) :=
  miuraOriginalEvenNLSFrequency_eq_Hill_frequency (m-1) n hn D a

/-- The comparison applies to ANY continuous realization of the original
NLS frequency with its actual high-regularity bracket values. Thus it does
not depend on our choice of representative for the unique extension. -/
theorem theorem3_corrected_for_any_original_frequency_extension (m : ℕ) (_hm : 1 ≤ m)
    (n : ℕ) (hn : 1 ≤ n) (f : MiuraRealSobolevSource (m-1) → ℂ)
    (hf : IsMiuraOriginalEvenFrequencyExtension (m-1) n f)
    (D : MiuraNativeHamiltonianActionData (m-1)) (a : MiuraRealSobolevSource (m-1)) :
    f a = D.frequency (n : ℤ) (miuraNativeActionMeanMap (m-1) a.val) :=
  congrFun (miuraOriginalEvenFrequencyExtension_unique (m-1) n hn f _ hf
    (D.sourceFrequency_original_extension n hn)) a

/-- A single open complex H^(m-1) neighborhood contains ALL original
real profiles and holomorphically extends the restricted original frequency. -/
theorem theorem3_frequency_holomorphic_extension (m : ℕ) (_hm : 1 ≤ m) (n : ℕ) (hn : 1 ≤ n) :
    ∃ U : Set (ScalarSobolev (m-1)), ∃ f : ScalarSobolev (m-1) → ℂ,
      IsOpen U ∧ (∀ a : MiuraRealSobolevSource (m-1), a.val ∈ U) ∧ AnalyticOnNhd ℂ f U ∧
        ∀ a : MiuraRealSobolevSource (m-1), f a.val = miuraOriginalEvenNLSFrequency (m-1) n hn a :=
  exists_common_open_analytic_miuraOriginalEvenNLSFrequency (m-1) n hn

/-- The all-order original-frequency construction agrees with the
independently normalized S₂ benchmark on the full real L² mass domain. -/
theorem theorem3_m1_frequency_normalization (n : ℕ) (hn : 1 ≤ n) (a : MiuraRealSobolevSource 0) :
    miuraOriginalEvenNLSFrequency 0 n hn a = 2*(Real.pi : ℂ)*(n : ℤ) := by
  obtain ⟨D⟩ := nonempty_miuraNativeHamiltonianActionData 0
  rw [miuraOriginalEvenNLSFrequency_eq_Hill_frequency 0 n hn D a]
  exact D.frequency_mass_eq a n (by omega)

end NLS.Articles.MKdVNLSHierarchies
