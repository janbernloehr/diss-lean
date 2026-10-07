import NLS.ZakharovShabat.SourceOrdinaryMass
import NLS.ZakharovShabat.SourceActionFiniteGapDifferential
import NLS.ZakharovShabat.PeriodOneSobolevHamiltonian
import NLS.ZakharovShabat.SourceSobolevEmbedding

/-! # The mass cotangent as the sum of original action cotangents

The real trace formula determines the complex analytic mass germ. Bounded
ℓ¹ summation then differentiates the full trace, and at finite gap the
result is a finite sum. The same formula holds on H¹ through the unchanged
coefficient inclusion.
-/
noncomputable section
open Set Complex Filter Topology NLS.Poisson
namespace NLS.ZakharovShabat

/-- The complex total action equals the physical mass on every real Hilbert source. -/
theorem SourceBirkhoffMapComplexData.hilbert_complexTotalAction_eq_mass
    {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) :
    sourceHilbertComplexTotalAction s φ.val = sourceHilbertMass φ.val := by
  rw [D.hilbert_complexTotalAction_eq_tsum φ.val (D.real_subset φ.property)]
  have hs := (D.summable_norm_hilbert_actions φ.val (D.real_subset φ.property)).of_norm
  apply Complex.ext
  · rw [Complex.re_tsum hs]
    have he := D.hilbert_totalAction_eq_mass φ
    rw [D.hilbert_totalAction_eq_tsum] at he
    convert he using 1
    apply tsum_congr
    intro n
    rw [sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n φ.val φ.property]
  · rw [Complex.im_tsum hs,sourceHilbertMass_eq_half_norm_sq_of_realType φ.val φ.property]
    simp only [(sourceComplexAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num) _
      φ.val φ.property).2.1,tsum_zero,Complex.ofReal_im]

/-- The full mass derivative is the absolutely convergent sum of all action derivatives. -/
theorem sourceHilbertMass_fderiv_eq_tsum_actions
    (φ : realTypeSourceSubmodule 2) (h : CoeffPair 2) :
    fderiv ℂ sourceHilbertMass φ.val h =
      ∑' n : ℤ, (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) φ.val) h := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  have he := eventuallyEq_source_of_analyticAt_of_real_agreement (by simp) φ
    (sourceHilbertComplexTotalAction s) sourceHilbertMass
    (D.hilbert_complexTotalAction_analytic φ.val (D.real_subset φ.property))
    (analyticOnNhd_sourceHilbertMass φ.val (mem_univ _)) D.hilbert_complexTotalAction_eq_mass
  rw [← he.fderiv_eq]
  exact D.hilbert_complexTotalAction_fderiv_apply φ.val (D.real_subset φ.property) h

/-- Any finite cutoff supporting the action cotangents computes the mass cotangent. -/
theorem sourceHilbertMass_fderiv_eq_finite_sum
    (φ : realTypeSourceSubmodule 2) (S : Finset ℤ)
    (hS : ∀ n ∉ S, fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) φ.val = 0)
    (h : CoeffPair 2) :
    fderiv ℂ sourceHilbertMass φ.val h =
      ∑ n ∈ S, (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) φ.val) h := by
  rw [sourceHilbertMass_fderiv_eq_tsum_actions]
  apply tsum_eq_sum
  intro n hn
  rw [hS n hn]
  rfl

/-- Sobolev mass is exactly the original Hilbert mass of the same coefficients. -/
theorem periodOneSobolevMass_eq_sourceHilbertMass (a : ScalarDomain 2 × ScalarDomain 2) :
    periodOneSobolevMass a = sourceHilbertMass (sobolevSourceInclusion a) := by
  rw [periodOneSobolevMass,Coeff.dualPairing_apply,sourceHilbertMass,reflectedHilbertPairing_apply,
    ← (Equiv.neg ℤ).tsum_eq (fun n => (sobolevSourceInclusion a).fst n * (sobolevSourceInclusion a).snd (-n))]
  apply tsum_congr
  intro n
  simp only [Coeff.reflection_apply,scalarInclusion_apply,sobolevSourceInclusion_fst,
    sobolevSourceInclusion_snd,neg_neg,Equiv.neg_apply]

/-- The full Sobolev mass derivative is the finite sum of original source action derivatives. -/
theorem periodOneSobolevMass_fderiv_eq_finite_sum
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a)))
    (S : Finset ℤ)
    (hS : ∀ n ∉ S, fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
      (sobolevSourceInclusion a) = 0) (h : ScalarDomain 2 × ScalarDomain 2) :
    fderiv ℂ periodOneSobolevMass a h =
      ∑ n ∈ S, (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
        (sobolevSourceInclusion a)) (sobolevSourceInclusion h) := by
  have he : periodOneSobolevMass = sourceHilbertMass ∘ sobolevSourceInclusion :=
    funext periodOneSobolevMass_eq_sourceHilbertMass
  rw [he,fderiv_comp a (analyticOnNhd_sourceHilbertMass _ (mem_univ _)).differentiableAt
    sobolevSourceInclusion.differentiableAt,ContinuousLinearMap.fderiv]
  exact sourceHilbertMass_fderiv_eq_finite_sum ⟨sobolevSourceInclusion a,ha⟩ S hS (sobolevSourceInclusion h)

end NLS.ZakharovShabat
