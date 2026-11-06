import NLS.MKdV.MiuraActionIndependence

/-! # Independence of the physical action cotangents and the mean

Every finite linear combination of the open physical action differentials
and the actual zero Fourier coefficient has unique coefficients. This
holds both for the ambient analytic L2 extensions and their actual
Frechet derivatives on the original H1 domain. Other gaps may be closed.
-/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraGardnerDirection_apply_fderiv (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) (j : ℤ) :
    l2GardnerDirection (miuraL2Action n) (scalarInclusion a) j =
      (2*I*(Real.pi : ℂ)*j)*(fderiv ℂ (miuraL2Action n) (scalarInclusion a))
        (lp.single 2 (-j) 1) := by
  rw [l2GardnerDirection,l2SpatialDerivative_apply _ (miuraActionGardner_memlp a ha n hn),
    l2ScalarGradient_apply]

theorem miuraActionCotangent_coefficients_unique (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j)))
    (S : Finset {n : ℕ // 1 ≤ n ∧ miuraMKdVAction a ha n ≠ 0})
    (c : {n : ℕ // 1 ≤ n ∧ miuraMKdVAction a ha n ≠ 0} → ℂ) (c₀ : ℂ)
    (hz : c₀ • lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0 +
      ∑ n ∈ S, c n • fderiv ℂ (miuraL2Action n.val) (scalarInclusion a) = 0) :
    c₀ = 0 ∧ ∀ n ∈ S, c n = 0 := by
  classical
  have hy : (∑ n ∈ S, c n • l2GardnerDirection (miuraL2Action n.val) (scalarInclusion a)) = 0 := by
    ext j
    have he := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L (lp.single 2 (-j) 1)) hz
    simp only [add_apply,smul_apply,sum_apply,smul_eq_mul,zero_apply] at he
    change c₀*(lp.single (E := fun _ : ℤ => ℂ) 2 (-j) 1) 0+
      ∑ n ∈ S, c n*(fderiv ℂ (miuraL2Action n.val) (scalarInclusion a)) (lp.single 2 (-j) 1) = 0 at he
    have hm : (2*I*(Real.pi : ℂ)*j)*(c₀*(lp.single (E := fun _ : ℤ => ℂ) 2 (-j) 1) 0) = 0 := by
      by_cases hj : j = 0
      · simp only [hj,Int.cast_zero,mul_zero,zero_mul]
      · simp [lp.single_apply,hj]
    have ht := congrArg (fun z : ℂ => (2*I*(Real.pi : ℂ)*j)*z) he
    rw [mul_add,hm,zero_add,mul_zero] at ht
    simp only [lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      lp.coeFn_zero,Pi.zero_apply]
    have hv (n : {n : ℕ // 1 ≤ n ∧ miuraMKdVAction a ha n ≠ 0}) :=
      miuraGardnerDirection_apply_fderiv a ha n.val n.property.1 j
    simp_rw [hv]
    calc
      _ = (2*I*(Real.pi : ℂ)*j)*
          (∑ n ∈ S, c n*(fderiv ℂ (miuraL2Action n.val) (scalarInclusion a)) (lp.single 2 (-j) 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = 0 := ht
  have hc := (linearIndependent_iff'.mp (linearIndependent_miuraGardnerDirections a ha)) S c hy
  have hs : (∑ n ∈ S, c n • fderiv ℂ (miuraL2Action n.val) (scalarInclusion a)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simpa only [hc n hn] using! (zero_smul ℂ (fderiv ℂ (miuraL2Action n.val) (scalarInclusion a)))
  rw [hs,add_zero] at hz
  have hm := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L (lp.single 2 0 1)) hz
  have hc₀ : c₀ = 0 := by
    change c₀*(lp.single (E := fun _ : ℤ => ℂ) 2 0 1) 0 = 0 at hm
    simpa only [lp.single_apply,Pi.single_eq_same,mul_one] using hm
  exact ⟨hc₀,hc⟩

theorem fderiv_miuraL2Action_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    fderiv ℂ (fun u : ScalarDomain 2 => miuraL2Action n (scalarInclusion u)) a =
      (fderiv ℂ (miuraL2Action n) (scalarInclusion a)).comp scalarInclusion := by
  have hmem := real_mem_miuraL2ActionDomain (scalarInclusion a)
    (by intro j; simpa only [scalarInclusion_apply] using ha j)
  exact (((analyticOnNhd_miuraL2Action n hn) _ hmem).differentiableAt.hasFDerivAt.comp a
    scalarInclusion.hasFDerivAt).fderiv

theorem miuraH1ActionCotangent_coefficients_unique (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j)))
    (S : Finset {n : ℕ // 1 ≤ n ∧ miuraMKdVAction a ha n ≠ 0})
    (c : {n : ℕ // 1 ≤ n ∧ miuraMKdVAction a ha n ≠ 0} → ℂ) (c₀ : ℂ)
    (hz : c₀ • WeightedCoeff.evalCLM (Weight.sobolev 1) 2 0 +
      ∑ n ∈ S, c n • fderiv ℂ (fun u : ScalarDomain 2 => miuraL2Action n.val (scalarInclusion u)) a = 0) :
    c₀ = 0 ∧ ∀ n ∈ S, c n = 0 := by
  classical
  apply miuraActionCotangent_coefficients_unique a ha S c c₀
  let L : Coeff 2 →L[ℂ] ℂ := c₀ • lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0+
    ∑ n ∈ S, c n • fderiv ℂ (miuraL2Action n.val) (scalarInclusion a)
  change L = 0
  apply ContinuousLinearMap.ext
  apply congrFun
  apply (scalarInclusion_denseRange (p := 2) (by simp)).equalizer L.continuous continuous_const
  funext h
  have he := congrArg (fun M : ScalarDomain 2 →L[ℂ] ℂ => M h) hz
  simp only [add_apply,smul_apply,sum_apply,smul_eq_mul,zero_apply] at he
  have hfd (n : {n : ℕ // 1 ≤ n ∧ miuraMKdVAction a ha n ≠ 0}) :=
    fderiv_miuraL2Action_H1 a ha n.val n.property.1
  simp_rw [hfd,ContinuousLinearMap.comp_apply] at he
  simp only [Function.comp_def,L,add_apply,smul_apply,sum_apply,smul_eq_mul]
  change c₀*(scalarInclusion h) 0+
    ∑ n ∈ S, c n*(fderiv ℂ (miuraL2Action n.val) (scalarInclusion a)) (scalarInclusion h) = 0
  simpa only [scalarInclusion_apply,WeightedCoeff.evalCLM_apply] using he

end NLS.MKdV
