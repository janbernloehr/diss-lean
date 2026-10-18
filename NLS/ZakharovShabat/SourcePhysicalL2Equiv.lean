import NLS.Fourier.UnitIntervalL2Equiv
import NLS.ZakharovShabat.SourcePhysicalL2

/-! # The exact physical Hilbert source equivalence

The unit-interval Fourier isometry on both components is exactly the
existing sourcePhysicalL2 map. In particular that map is bijective and
preserves the original Hilbert norm, improving its earlier bound.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat
open NLS.Fourier

/-- The physical source equivalence preserves the sum of both component energies. -/
def sourcePhysicalL2Equiv : CoeffPair 2 ≃ₗᵢ[ℂ] IntervalPairL2 :=
  unitL2SynthesisEquiv.withLpProdCongr 2 unitL2SynthesisEquiv

/-- The isometry is exactly the established source-to-physical L2 map. -/
theorem sourcePhysicalL2Equiv_eq : (sourcePhysicalL2Equiv : CoeffPair 2 → IntervalPairL2) =
    sourcePhysicalL2 := by
  apply CoeffPair.eq_of_continuous_of_finsupp (by simp) _ _
    sourcePhysicalL2Equiv.continuous sourcePhysicalL2.continuous
  intro a
  apply intervalL2Representative_injective
  have h1 := unitL2SynthesisEquiv_ofFinsupp a.1
  have h2 := unitL2SynthesisEquiv_ofFinsupp a.2
  have hp := (sourcePhysicalL2_representative (CoeffPair.ofFinsupp a)).trans
    (ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc_right (by norm_num : (1:ℝ) ≤ 2)) (physicalBase_periodOnePotential_finite a))
  filter_upwards [h1,h2,hp] with x hx hy hz
  exact (Prod.ext hx hy).trans hz.symm

/-- The explicit equivalence evaluates to the existing physical source class. -/
@[simp] theorem sourcePhysicalL2Equiv_apply (φ : CoeffPair 2) :
    sourcePhysicalL2Equiv φ = sourcePhysicalL2 φ := congrFun sourcePhysicalL2Equiv_eq φ

/-- The actual source-to-physical map is bijective on all complex Hilbert inputs. -/
theorem sourcePhysicalL2_bijective : Function.Bijective sourcePhysicalL2 := by
  rw [← sourcePhysicalL2Equiv_eq]
  exact sourcePhysicalL2Equiv.bijective

/-- The actual physical source map preserves the exact original Hilbert norm. -/
theorem norm_sourcePhysicalL2 (φ : CoeffPair 2) : ‖sourcePhysicalL2 φ‖ = ‖φ‖ := by
  rw [← sourcePhysicalL2Equiv_apply]
  exact sourcePhysicalL2Equiv.norm_map φ

/-- The original unit-interval Fourier integrals recover both source components. -/
theorem sourcePhysicalL2_coefficients (φ : CoeffPair 2) (n : ℤ) :
    intervalFourierCoefficient 1 (sourcePhysicalL2 φ).ofLp.1 n = φ.fst n ∧
    intervalFourierCoefficient 1 (sourcePhysicalL2 φ).ofLp.2 n = φ.snd n := by
  rw [← sourcePhysicalL2Equiv_apply]
  exact ⟨unitL2SynthesisLinear_coefficient φ.fst n,unitL2SynthesisLinear_coefficient φ.snd n⟩

/-- The inverse equivalence recovers every original physical L2 class. -/
@[simp] theorem sourcePhysicalL2_equiv_symm (u : IntervalPairL2) :
    sourcePhysicalL2 (sourcePhysicalL2Equiv.symm u) = u := by
  rw [← sourcePhysicalL2Equiv_apply,LinearIsometryEquiv.apply_symm_apply]

/-- The first inverse coefficient is its literal unit-interval Fourier integral. -/
@[simp] theorem sourcePhysicalL2Equiv_symm_fst (u : IntervalPairL2) (n : ℤ) :
    (sourcePhysicalL2Equiv.symm u).fst n = intervalFourierCoefficient 1 u.ofLp.1 n :=
  unitL2SynthesisEquiv_symm_coefficient u.ofLp.1 n

/-- The second inverse coefficient is its literal unit-interval Fourier integral. -/
@[simp] theorem sourcePhysicalL2Equiv_symm_snd (u : IntervalPairL2) (n : ℤ) :
    (sourcePhysicalL2Equiv.symm u).snd n = intervalFourierCoefficient 1 u.ofLp.2 n :=
  unitL2SynthesisEquiv_symm_coefficient u.ofLp.2 n

end NLS.ZakharovShabat
