import NLS.KdV.HillFinitePhysicalPotential
import NLS.KdV.HillHminusOriginalSourceAdapter
import Mathlib.Order.Filter.AtTopBot.Interval

/-! # Smooth original physical approximants in every native Sobolev topology

Symmetric raw Fourier truncation gives real smooth unit-period potentials
of the same mean, converging to the given datum in its actual H^s norm.
No L2 bound or spectral chart is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ComplexConjugate ContDiff
namespace NLS.KdV

/-- Original physical finite Fourier coefficients retain the exact unit modes. -/
theorem hillContinuousCoefficients_finitePhysical_even (a : ℤ →₀ ℂ) (j : ℤ) :
    (hillContinuousCoefficients (hillFinitePhysicalPotential a)).val (2*j)=a j := by
  rw [hillContinuousCoefficients_finitePhysical]
  change (hillForgetWeight SpectralWeight.one 2 (hillPeriodOnePotential SpectralWeight.one
    (WeightedCoeff.ofFinsupp SpectralWeight.one.doubleIndex.toWeight 2 a))).val (2*j)=_
  rw [hillForgetWeight_apply, hillPeriodOnePotential_even, WeightedCoeff.ofFinsupp_apply]

/-- Every real mean-zero native H^s datum is the H^s limit of actual smooth
real mean-zero unit-period physical potentials. This holds for every real s. -/
theorem exists_smooth_original_physical_sobolev_approximation
    {s : ℝ} (q : WeightedCoeff (Weight.sobolev s) 2)
    (hr : ∀ j : ℤ, q.val (-j)=conj (q.val j)) (hm : q.val 0=0) :
    ∃ (Q : ℕ → C(AddCircle (2 : ℝ), ℂ))
      (v : ℕ → WeightedCoeff (Weight.sobolev s) 2),
      (∀ i x, (Q i x).im=0) ∧
      (∀ i, ContDiff ℝ ∞ (fun x : ℝ => Q i (x : AddCircle (2 : ℝ)))) ∧
      (∀ i, Function.Periodic (fun x : ℝ => Q i (x : AddCircle (2 : ℝ))) 1) ∧
      (∀ i, (∫ x in (0 : ℝ)..1, Q i (x : AddCircle (2 : ℝ)))=0) ∧
      (∀ i j, (v i).val j=(hillContinuousCoefficients (Q i)).val (2*j)) ∧
      Tendsto v atTop (𝓝 q) ∧
      (∀ i, (∀ j : ℤ, (v i).val (-j)=conj ((v i).val j)) ∧ (v i).val 0=0) := by
  classical
  let S (i : ℕ) : Finset ℤ := Finset.Icc (-(i : ℤ)) i
  let v (i : ℕ) := WeightedCoeff.truncate (Weight.sobolev s) 2 (S i) q
  let a (i : ℕ) : ℤ →₀ ℂ := Finsupp.onFinset (S i) (v i).val
    (by intro j hj; by_contra he; exact hj (by simp [v, he]))
  have ha (i : ℕ) (j : ℤ) : a i j=if j∈S i then q.val j else 0 := by
    simp only [a, Finsupp.onFinset_apply, v, WeightedCoeff.truncate_apply]
  have har (i : ℕ) : ∀ j : ℤ, a i (-j)=conj (a i j) := by
    intro j
    have hneg : -j∈S i ↔ j∈S i := by simp only [S, Finset.mem_Icc]; omega
    by_cases hj : j∈S i <;> simp [ha, hneg, hj, hr j]
  have ham (i : ℕ) : a i 0=0 := by simp only [ha, hm, ite_self]
  refine ⟨(fun i => hillFinitePhysicalPotential (a i)), v,
    (fun i => real_hillFinitePhysicalPotential _ (har i)),
    (fun i => contDiff_hillFinitePhysicalPotential _),
    (fun i => periodic_hillFinitePhysicalPotential _),
    (fun i => (mean_hillFinitePhysicalPotential _).trans (ham i)), ?_, ?_⟩
  · intro i j
    rw [hillContinuousCoefficients_finitePhysical_even, ha]
    exact WeightedCoeff.truncate_apply (Weight.sobolev s) 2 (S i) q j
  · refine ⟨?_, ?_⟩
    · exact (WeightedCoeff.tendsto_truncate (Weight.sobolev s) 2 (by simp) q).comp
        Finset.tendsto_Icc_neg
    · intro i
      have he (j : ℤ) : (v i).val j=a i j := by
        simp only [v, WeightedCoeff.truncate_apply, ha]
      exact ⟨(fun j => by rw [he, he]; exact har i j), by rw [he]; exact ham i⟩

end NLS.KdV
