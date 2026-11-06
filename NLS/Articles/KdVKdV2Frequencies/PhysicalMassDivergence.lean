import NLS.KdV.HillContinuousQuadraticMass
import NLS.KdV.HillPhysicalSobolevApproximation

/-! # The global physical mass obstruction in Theorem 1.12(v)

At every genuinely non-L2 real mean-zero H^s datum, -1 ≤ s, actual smooth
physical approximants exist in that SAME Sobolev topology and their actual
H_0 diverges. Thus the physical quadratic invariant has no continuous
extension at any such datum. The exact 20*(2*n*pi)*H_0 term in the KdV2
frequency formula diverges as well. Identifying the full frequency and
controlling its renormalized correction remain separate obligations.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ComplexConjugate ContDiff
open NLS.KdV
namespace NLS.Articles.KdVKdV2Frequencies

/-- The actual physical H_0 diverges along EVERY real continuous physical
approximation in the native H^s topology, including the full -1 < s < 0
range of Theorem 1.12(v), at EVERY non-L2 datum. -/
theorem tendsto_physical_H0_atTop_of_nonL2_sobolev_limit
    {ι : Type*} {l : Filter ι} {s : ℝ} (hs : -1 ≤ s)
    (q : WeightedCoeff (Weight.sobolev s) 2) (hq : ¬ Memℓp q.val 2)
    (Q : ι → C(AddCircle (2 : ℝ), ℂ))
    (hr : ∀ i x, (Q i x).im=0)
    (hp : ∀ i, Function.Periodic (fun x : ℝ => Q i (x : AddCircle (2 : ℝ))) 1)
    (v : ι → WeightedCoeff (Weight.sobolev s) 2)
    (hv : ∀ i j, (v i).val j=(hillContinuousCoefficients (Q i)).val (2*j))
    (ht : Tendsto v l (𝓝 q)) :
    Tendsto (fun i => (classicalQuadraticInvariant
      (fun x : ℝ => Q i (x : AddCircle (2 : ℝ)))).re) l atTop := by
  simp_rw [classicalQuadraticInvariant_re_eq_half_hillContinuousCoefficients_norm_sq
    _ (hr _) (hp _)]
  exact tendsto_original_half_L2_norm_sq_atTop_of_nonL2_sobolev_limit hs q hq _ v hv ht

/-- Actual smooth real mean-zero physical approximants with diverging H_0
exist at EVERY genuinely non-L2 real mean-zero native H^s datum. -/
theorem exists_smooth_physical_approximation_with_H0_divergence
    {s : ℝ} (hs : -1 ≤ s) (q : WeightedCoeff (Weight.sobolev s) 2)
    (hr : ∀ j : ℤ, q.val (-j)=conj (q.val j)) (hm : q.val 0=0)
    (hq : ¬ Memℓp q.val 2) :
    ∃ (Q : ℕ → C(AddCircle (2 : ℝ), ℂ))
      (v : ℕ → WeightedCoeff (Weight.sobolev s) 2),
      (∀ i x, (Q i x).im=0) ∧
      (∀ i, ContDiff ℝ ∞ (fun x : ℝ => Q i (x : AddCircle (2 : ℝ)))) ∧
      (∀ i, Function.Periodic (fun x : ℝ => Q i (x : AddCircle (2 : ℝ))) 1) ∧
      (∀ i, (∫ x in (0 : ℝ)..1, Q i (x : AddCircle (2 : ℝ)))=0) ∧
      (∀ i j, (v i).val j=(hillContinuousCoefficients (Q i)).val (2*j)) ∧
      Tendsto v atTop (𝓝 q) ∧
      (∀ i, (∀ j : ℤ, (v i).val (-j)=conj ((v i).val j)) ∧ (v i).val 0=0) ∧
      Tendsto (fun i => (classicalQuadraticInvariant
        (fun x : ℝ => Q i (x : AddCircle (2 : ℝ)))).re) atTop atTop := by
  obtain ⟨Q, v, hreal, hsmooth, hperiodic, hmean, hv, ht, hvreal⟩ :=
    exists_smooth_original_physical_sobolev_approximation q hr hm
  exact ⟨Q, v, hreal, hsmooth, hperiodic, hmean, hv, ht, hvreal,
    tendsto_physical_H0_atTop_of_nonL2_sobolev_limit hs q hq Q hreal hperiodic v hv ht⟩

/-- No real-valued extension agreeing with the ACTUAL smooth physical H_0
can be continuous, even WITHIN the real mean-zero subspace, at ANY non-L2
H^s datum. This is the mass
obstruction, not yet the full KdV2 frequency or solution-map obstruction. -/
theorem not_continuousWithinAt_physical_H0_extension_of_nonL2
    {s : ℝ} (hs : -1 ≤ s) (q : WeightedCoeff (Weight.sobolev s) 2)
    (hr : ∀ j : ℤ, q.val (-j)=conj (q.val j)) (hm : q.val 0=0)
    (hq : ¬ Memℓp q.val 2) (F : WeightedCoeff (Weight.sobolev s) 2 → ℝ)
    (hF : ∀ (Q : C(AddCircle (2 : ℝ), ℂ))
      (v : WeightedCoeff (Weight.sobolev s) 2),
      (∀ x, (Q x).im=0) →
      ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) →
      Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1 →
      (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ)))=0 →
      (∀ j, v.val j=(hillContinuousCoefficients Q).val (2*j)) →
      F v=(classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))).re) :
    ¬ ContinuousWithinAt F
      {u | (∀ j : ℤ, u.val (-j)=conj (u.val j)) ∧ u.val 0=0} q := by
  intro hc
  obtain ⟨Q, v, hreal, hsmooth, hperiodic, hmean, hv, ht, hvreal, hdiv⟩ :=
    exists_smooth_physical_approximation_with_H0_divergence hs q hr hm hq
  have he (i : ℕ) := hF (Q i) (v i) (hreal i) (hsmooth i) (hperiodic i) (hmean i) (hv i)
  have hwithin : Tendsto v atTop
      (𝓝[{u | (∀ j : ℤ, u.val (-j)=conj (u.val j)) ∧ u.val 0=0}] q) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall hvreal⟩
  have hfinite := hc.tendsto.comp hwithin
  simp only [Function.comp_def, he] at hfinite
  exact not_tendsto_nhds_of_tendsto_atTop hdiv (F q) hfinite

/-- Exact divergent physical mass contribution in the printed KdV2 formula,
for EVERY positive mode, at arbitrary non-L2 native H^s limits. -/
theorem tendsto_kdv2_physical_mass_term_atTop_of_nonL2_sobolev_limit
    {ι : Type*} {l : Filter ι} {s : ℝ} (hs : -1 ≤ s)
    (q : WeightedCoeff (Weight.sobolev s) 2) (hq : ¬ Memℓp q.val 2)
    (Q : ι → C(AddCircle (2 : ℝ), ℂ))
    (hr : ∀ i x, (Q i x).im=0)
    (hp : ∀ i, Function.Periodic (fun x : ℝ => Q i (x : AddCircle (2 : ℝ))) 1)
    (v : ι → WeightedCoeff (Weight.sobolev s) 2)
    (hv : ∀ i j, (v i).val j=(hillContinuousCoefficients (Q i)).val (2*j))
    (ht : Tendsto v l (𝓝 q)) (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun i => 20*(2*(n : ℝ)*Real.pi)*
      (classicalQuadraticInvariant (fun x : ℝ => Q i (x : AddCircle (2 : ℝ)))).re)
      l atTop :=
  (tendsto_physical_H0_atTop_of_nonL2_sobolev_limit hs q hq Q hr hp v hv ht).const_mul_atTop
    (by positivity)

end NLS.Articles.KdVKdV2Frequencies
