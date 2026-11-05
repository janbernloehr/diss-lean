import NLS.KdV.HillGapRootEnergyProduct
import NLS.KdV.HillGapBoxNumeratorReality

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillGapFullEnergyProduct_factorization
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (k : ℕ) (E : ℂ) :
    hillAbelianNumeratorProduct roots 0 E =
      hillGapRootEnergyFactor roots k E*hillAbelianNumeratorProduct roots (k+1) E := by
  let f := fun j => hillAbelianNumeratorFactor roots 0 j E
  let g := fun j => hillAbelianNumeratorFactor roots (k+1) j E
  have he (j : ℕ) : (if j = k then 1 else f j) = g j := by
    dsimp only [f,g,hillAbelianNumeratorFactor]
    by_cases hj : j = k
    · subst j
      simp only [ite_true]
    · simp only [if_neg hj,if_neg (by omega : j+1 ≠ 0),if_neg (by omega : j+1 ≠ k+1)]
  have hu : Function.update f k 1 = g := by
    funext j
    rw [Function.update_apply]
    exact he j
  have hm : Multipliable (Function.update f k 1) := by
    rw [hu]
    exact multipliable_hillAbelianNumeratorFactors q hq hr roots hroots (k+1) E
  have hp := Multipliable.tprod_eq_mul_tprod_ite' (f := f) k hm
  simp_rw [he] at hp
  have hk : f k = hillGapRootEnergyFactor roots k E := by
    simp only [f,hillAbelianNumeratorFactor,if_neg (by omega : k+1 ≠ 0)]
  rw [hk] at hp
  exact hp

theorem hillGapFullEnergyProduct_deriv_at_root
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (k : ℕ) :
    deriv (hillAbelianNumeratorProduct roots 0) (roots k : ℂ) =
      -hillAbelianNumeratorProduct roots (k+1) (roots k : ℂ)/(freeHillValue (k+1 : ℕ) : ℂ) := by
  have hd := (((hasDerivAt_id (roots k : ℂ)).const_sub (roots k : ℂ)).div_const
    (freeHillValue (k+1 : ℕ) : ℂ)).mul
    ((analyticOnNhd_hillAbelianNumeratorProduct q hq hr roots hroots (k+1))
      (roots k) (mem_univ _)).differentiableAt.hasDerivAt
  have hfun : (fun E => ((roots k : ℂ)-E)/(freeHillValue (k+1 : ℕ) : ℂ)*
      hillAbelianNumeratorProduct roots (k+1) E) = hillAbelianNumeratorProduct roots 0 := by
    funext E
    exact (hillGapFullEnergyProduct_factorization q hq hr roots hroots k E).symm
  change HasDerivAt (fun E => ((roots k : ℂ)-E)/(freeHillValue (k+1 : ℕ) : ℂ)*
    hillAbelianNumeratorProduct roots (k+1) E) _ _ at hd
  rw [hfun] at hd
  convert hd.deriv using 1
  dsimp only [id]
  ring

theorem hillGapFullEnergyProduct_simple_zeros
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (E : ℂ)
    (hzero : hillAbelianNumeratorProduct roots 0 E = 0) :
    deriv (hillAbelianNumeratorProduct roots 0) E ≠ 0 := by
  obtain ⟨k,_,rfl⟩ := (hillAbelianNumeratorProduct_zero_iff q hq hr roots hroots 0 E).mp hzero
  rw [hillGapFullEnergyProduct_deriv_at_root q hq hr roots hroots k]
  have hne := hillAbelianPsiCandidate_ne_zero_on_own_gap q hq hr roots hroots (k+1) (by omega) (roots k)
    (ofReal_mem_ordered_segment _ _ _ (monotone_hillRealLabels q hq hr (by omega)) (hroots k))
  have hp : hillAbelianNumeratorProduct roots (k+1) (roots k : ℂ) ≠ 0 := by
    intro h
    apply hne
    rw [hillAbelianPsiCandidate,h,mul_zero]
  exact div_ne_zero (neg_ne_zero.mpr hp) (hillGapRootEnergyFactor_denominator_ne_zero k)

end NLS.KdV
