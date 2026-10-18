import NLS.Fourier.BoundedLatticeFourierDifference
import NLS.SequenceSpaces.WeightedMultiplier

/-! # Weighted L2 bounds for Fourier sampling errors

A weighted supremum bound on the displacement transfers to the same weighted L2 bound on the literal Fourier sampling error.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.Fourier

/-- Any weighted supremum bound on the actual displacements transfers
to the same weighted L2 bound on the actual sampling error. -/
theorem exists_weighted_lattice_fourier_difference
    (f : ℝ → ℂ) (hf : Continuous f) (δ : NLS.Coeff ⊤)
    (w : NLS.Weight) (M : ℝ) (hM : 0 ≤ M) (hδ : ∀ n, w n*‖δ n‖ ≤ M) :
    ∃ e : NLS.WeightedCoeff w 2,
      (∀ n, e.val n = (∫ x in (0:ℝ)..1, f x*exp (-2*I*((Real.pi:ℂ)*n+δ n)*x))-
        periodOneCoefficient f n) ∧
      ‖e‖ ≤ M*((2*Real.exp (2*‖δ‖))*
        ‖unitIntervalMemLpCoefficients f (memLp_two_interval hf 0 1 (by norm_num))‖) := by
  obtain ⟨r,hr,_,hn⟩ := exists_bounded_lattice_fourier_difference f hf δ
  let r₀ := (NLS.WeightedCoeff.weightIsometry NLS.Weight.one 2).symm r
  have hr₀ (n : ℤ) : r₀.val n = r n := by
    change r n/(NLS.Weight.one n:ℂ) = r n
    simp
  have hn₀ : ‖r₀‖ = ‖r‖ := (NLS.WeightedCoeff.weightIsometry NLS.Weight.one 2).symm.norm_map r
  have hmult (n : ℤ) : w n*‖δ n‖ ≤ M*NLS.Weight.one n := by simpa using hδ n
  let e := NLS.WeightedCoeff.weightedMultiplier NLS.Weight.one w δ M hmult r₀
  refine ⟨e,?_,?_⟩
  · intro n
    change δ n*r₀.val n = _
    rw [hr₀]
    exact (hr n).symm
  · have hh := NLS.WeightedCoeff.norm_weightedMultiplier_le NLS.Weight.one w δ M hM hmult r₀
    rw [hn₀] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hn hM)

/-- In particular, inverse-index displacements give one derivative of
square summability in the literal shifted-sample minus Fourier error. -/
theorem exists_h1_lattice_fourier_difference
    (f : ℝ → ℂ) (hf : Continuous f) (δ : NLS.Coeff ⊤)
    (M : ℝ) (hM : 0 ≤ M) (hδ : ∀ n : ℤ, (1+|(n:ℝ)|)*‖δ n‖ ≤ M) :
    ∃ e : NLS.WeightedCoeff (NLS.Weight.sobolev 1) 2,
      (∀ n, e.val n = (∫ x in (0:ℝ)..1, f x*exp (-2*I*((Real.pi:ℂ)*n+δ n)*x))-
        periodOneCoefficient f n) ∧
      ‖e‖ ≤ M*((2*Real.exp (2*‖δ‖))*
        ‖unitIntervalMemLpCoefficients f (memLp_two_interval hf 0 1 (by norm_num))‖) :=
  exists_weighted_lattice_fourier_difference f hf δ (NLS.Weight.sobolev 1) M hM
    (by simpa only [NLS.Weight.sobolev_apply,Real.rpow_one] using hδ)

end NLS.Fourier
