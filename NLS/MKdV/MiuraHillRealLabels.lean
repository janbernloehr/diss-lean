import NLS.MKdV.MiuraHillSpectralIdentification

/-! # Intrinsic ordered labels of the physical real H¹ Miura Hill spectrum

Fourier reality of the actual Miura potential allows the existing global
Hill labeling theorem to apply. All resulting labels are nonnegative.
The labeling is intrinsic and has the actual analytic multiplicities;
matching each fixed index with its NLS square is a separate next step.
-/
noncomputable section
open Set Complex NLS.Fourier NLS.ZakharovShabat NLS.KdV
open scoped ComplexConjugate ENNReal
namespace NLS.MKdV

theorem sobolevMiuraHillPotential_real (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) : IsRealHillPotential (sobolevMiuraHillPotential a) := by
  let f : ℝ → ℂ := fun x => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))
  have he : sobolevConjugateCLM a = a := by
    apply Subtype.ext
    funext n
    simpa only [sobolevConjugateCLM_apply] using (ha n).symm
  have hfstar : (fun x => conj (f x)) = f := by
    funext x
    have h := periodOneSobolevSynthesis_conjugate a x
    rw [he] at h
    exact h.symm
  have hdstar : ∀ x, conj (deriv f x) = deriv f x := by
    have h : deriv (fun x => conj (f x)) = fun x => conj (deriv f x) := deriv.star'
    rw [hfstar] at h
    intro x
    exact (congrFun h x).symm
  have hqstar : (fun x => conj (miuraPotential f x)) = miuraPotential f := by
    funext x
    simp only [miuraPotential,map_add,map_pow,hdstar x,congrFun hfstar x]
  have hunit (n : ℤ) : sobolevMiuraUnitPotential a (-n) = conj (sobolevMiuraUnitPotential a n) := by
    rw [sobolevMiuraUnitPotential_physical,sobolevMiuraUnitPotential_physical]
    change periodOneCoefficient (miuraPotential f) (-n) = conj (periodOneCoefficient (miuraPotential f) n)
    have h := unitFourierCoefficient_conj (miuraPotential f) (-n)
    rw [hqstar] at h
    simpa only [neg_neg,unitFourierCoefficient_eq_fourierCoeffOn,periodOneCoefficient] using h
  intro k
  change Coeff.periodDouble (sobolevMiuraUnitPotential a) (-k) =
    conj (Coeff.periodDouble (sobolevMiuraUnitPotential a) k)
  by_cases hk : k % 2 = 0
  · have he : k = 2*(k/2) := by omega
    rw [he,← mul_neg,Coeff.periodDouble_even,Coeff.periodDouble_even]
    exact hunit _
  · have he : k = 2*(k/2)+1 := by omega
    rw [he,show -(2*(k/2)+1) = 2*(-(k/2)-1)+1 by ring,
      Coeff.periodDouble_odd,Coeff.periodDouble_odd,map_zero]

def miuraHillLabels (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n))) : ℕ → ℝ :=
  hillRealLabels (sobolevMiuraWeightedPotential a) (by
    rw [toCoeff_sobolevMiuraWeightedPotential]
    exact sobolevMiuraHillPotential_even a) (by
    rw [toCoeff_sobolevMiuraWeightedPotential]
    exact sobolevMiuraHillPotential_real a ha)

theorem monotone_miuraHillLabels (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n))) :
    Monotone (miuraHillLabels a ha) := monotone_hillRealLabels _ _ _

theorem miuraHillLabels_root_iff (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n))) (μ : ℂ) :
    hillL2Radicand (sobolevMiuraHillPotential a) μ = 0 ↔
      ∃ j : ℕ, μ = (miuraHillLabels a ha j : ℂ) := by
  simpa only [miuraHillLabels,toCoeff_sobolevMiuraWeightedPotential] using!
    hillRealLabels_root_iff (sobolevMiuraWeightedPotential a) _ _ μ

theorem miuraHillLabels_nonnegative (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n)))
    (j : ℕ) : 0 ≤ miuraHillLabels a ha j := by
  have hz := (miuraHillLabels_root_iff a ha (miuraHillLabels a ha j)).mpr ⟨j,rfl⟩
  exact (miuraHillRadicand_root_nonnegative a ha _ hz).2

theorem miuraHillLabels_multiplicity (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n)))
    (x : ℝ) :
    {j : ℕ | miuraHillLabels a ha j = x}.Finite ∧
      (∑ᶠ j : ℕ, if miuraHillLabels a ha j = x then (1 : ℕ) else 0) =
        analyticOrderNatAt (hillL2Radicand (sobolevMiuraHillPotential a)) x := by
  simpa only [miuraHillLabels,toCoeff_sobolevMiuraWeightedPotential] using!
    hillRealLabels_global_multiplicity (sobolevMiuraWeightedPotential a) _ _ x

end NLS.MKdV
