import NLS.Articles.KdVConvexity.DirichletCoordinateDifferential
import NLS.KdV.HillHminusOneFreeDirichletDifferential

/-! # The complete bounded Fourier derivative of the actual Hilbert energy map

The operator retains the mean and both signed frequencies. The negative
Sobolev weight and positive sampling give exactly 1/(1+n), without a
finite-support restriction. Equality is of full bounded derivatives.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.Articles.KdVConvexity
open NLS.KdV

def freeNormalizedDirichletLinearization : PeriodOneHminusOne →L[ℂ] Coeff 2 :=
  let W := (WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2).toContinuousLinearEquiv.toContinuousLinearMap
  let S := Coeff.hilbertSampleCLM positiveDirichletIndex
  let R := (Coeff.reflection (p := 2)).toContinuousLinearEquiv.toContinuousLinearMap
  (WeightedCoeff.evalCLM (Weight.sobolev (-1)) 2 0).smulRight dirichletReciprocal-
    (1/2 : ℂ) • (S.comp W+S.comp (R.comp W))

theorem freeNormalizedDirichletLinearization_apply (h : PeriodOneHminusOne) (k : ℤ) :
    freeNormalizedDirichletLinearization h k =
      (h.val 0-(h.val (actionIndexEquiv k : ℤ)+h.val (-(actionIndexEquiv k : ℤ)))/2)/
        (1+(actionIndexEquiv k : ℕ) : ℂ) := by
  have hw : (Weight.sobolev (-1) (actionIndexEquiv k : ℤ) : ℂ) =
      (1+(actionIndexEquiv k : ℕ) : ℂ)⁻¹ := by
    simp only [Weight.sobolev_apply,Real.rpow_neg_one,Int.cast_natCast,
      abs_of_nonneg (show (0 : ℝ) ≤ ((actionIndexEquiv k : ℕ) : ℝ) from Nat.cast_nonneg _),Complex.ofReal_inv,
      Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_natCast]
  have hb : (baseActionWeight k : ℂ) = (1+(actionIndexEquiv k : ℕ) : ℂ)⁻¹ := by
    simp only [baseActionWeight,Complex.ofReal_inv,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_natCast]
  change h.val 0*(baseActionWeight k : ℂ)-(1/2 : ℂ)*
    ((Weight.sobolev (-1) (actionIndexEquiv k : ℤ) : ℂ)*h.val (actionIndexEquiv k : ℤ)+
      (Weight.sobolev (-1) (-(actionIndexEquiv k : ℤ)) : ℂ)*h.val (-(actionIndexEquiv k : ℤ))) = _
  rw [Weight.sobolev_neg,hw,hb]
  ring

theorem normalizedDirichletEnergyMap_hasFDerivAt_zero
    (Ω : Set PeriodOneHminusOne) (E : PeriodOneHminusOne → Coeff 2)
    (hΩ : IsOpen Ω) (h0 : (0 : PeriodOneHminusOne) ∈ Ω) (hE : AnalyticOnNhd ℂ E Ω) (hE0 : E 0 = 0)
    (hroot : ∀ p ∈ Ω, ∀ n : ℕ+, hillHminusDirichlet p
      ((freeHillValue (n : ℕ) : ℂ)+(1+(n : ℕ) : ℂ)*E p (actionIndexEquiv.symm n)) = 0) :
    HasFDerivAt E freeNormalizedDirichletLinearization 0 := by
  have hr : IsRealPeriodOneHminusOne 0 := by intro k; simp
  have hd : fderiv ℂ E 0 = freeNormalizedDirichletLinearization := by
    apply ContinuousLinearMap.ext
    intro h
    ext k
    let n := actionIndexEquiv k
    have hEq : E 0 (actionIndexEquiv.symm n) =
        ((hillHminusDirichletEnergy 0 hr n : ℂ)-(freeHillValue (n : ℕ) : ℂ))/(1+(n : ℕ) : ℂ) := by
      rw [hE0,hillHminusDirichletEnergy_zero_potential,sub_self,zero_div]
      rfl
    have hh := normalizedDirichletCoordinate_fderiv Ω E hΩ hE hroot 0 h0 hr n hEq h
    rw [hillHminusDirichletEnergy_zero_potential,hillHminusWeakPotential_free_Dirichlet_square,
      hillHminusDirichletColumn_free_square_integral] at hh
    simp only [n,Equiv.symm_apply_apply] at hh
    rw [freeNormalizedDirichletLinearization_apply,hh]
    have hn : (actionIndexEquiv k : ℂ) ≠ 0 := by exact_mod_cast (actionIndexEquiv k).ne_zero
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    ring
  rw [← hd]
  exact (hE 0 h0).differentiableAt.hasFDerivAt

theorem exists_global_analytic_normalized_Dirichlet_energies_with_free_linearization :
    ∃ Ω : Set PeriodOneHminusOne, ∃ E : PeriodOneHminusOne → Coeff 2,
      IsOpen Ω ∧ {q | IsRealPeriodOneHminusOne q} ⊆ Ω ∧ AnalyticOnNhd ℂ E Ω ∧
      (∀ p ∈ Ω, ∀ n : ℕ+, hillHminusDirichlet p
        ((freeHillValue (n : ℕ) : ℂ)+(1+(n : ℕ) : ℂ)*E p (actionIndexEquiv.symm n)) = 0) ∧
      (∀ p (hp : IsRealPeriodOneHminusOne p) (n : ℕ+),
        E p (actionIndexEquiv.symm n) =
          ((hillHminusDirichletEnergy p hp n : ℂ)-(freeHillValue (n : ℕ) : ℂ))/(1+(n : ℕ) : ℂ)) ∧
      E 0 = 0 ∧ HasFDerivAt E freeNormalizedDirichletLinearization 0 := by
  obtain ⟨Ω,E,hΩ,hreal,hE,hroot,hrec,hzero⟩ := exists_global_analytic_normalized_Dirichlet_energies
  have hr : IsRealPeriodOneHminusOne 0 := by intro k; simp
  exact ⟨Ω,E,hΩ,hreal,hE,hroot,hrec,hzero,
    normalizedDirichletEnergyMap_hasFDerivAt_zero Ω E hΩ (hreal hr) hE hzero hroot⟩

end NLS.Articles.KdVConvexity
