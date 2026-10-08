import NLS.ZakharovShabat.SourceHigherSobolevTraceTransfer

/-! # Limits of physical finite-gap Hamiltonians in the Hˢ topology

Every real Hˢ source has actual spectral finite-gap approximants. Their
higher-action sequences converge in ℓ¹ and their independently defined
physical Hamiltonians converge to the correctly normalized action sums.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ZakharovShabat
variable (s : ℕ)

/-- Hˢ convergence of real sources implies ℓ¹ convergence of each higher-action
sequence through level 2s+1, not only convergence of individual actions. -/
theorem tendsto_sourceHigherSobolevHigherActionSequence
    (a : realTypeHigherSobolevSourceLocus s) (b : ℕ → realTypeHigherSobolevSourceLocus s)
    (hb : Tendsto b atTop (𝓝 a)) (k : ℕ) (hk : k ≤ 2*s) :
    Tendsto (fun j => sourceHigherSobolevHigherActionSequence s k (b j).val) atTop
      (𝓝 (sourceHigherSobolevHigherActionSequence s k a.val)) := by
  obtain ⟨U,_,haU,hA⟩ := exists_local_sourceHigherSobolevHigherActionSequence_analytic s a.val a.property
  exact (((hA k hk).2 a.val haU).continuousAt.comp continuous_subtype_val.continuousAt).tendsto.comp hb

/-- The physical hierarchy along any convergent finite-gap approximation has
the limit dictated by the actual absolutely convergent higher-action trace. -/
theorem tendsto_sourceHigherSobolevFiniteGapHamiltonian
    (a : realTypeHigherSobolevSourceLocus s) (b : ℕ → realTypeHigherSobolevSourceLocus s)
    (hb : ∀ j, b j ∈ sourceHigherSobolevFiniteGapLocus s)
    (hlim : Tendsto b atTop (𝓝 a)) (k : ℕ) (hk : k ≤ 2*s) :
    Tendsto (fun j => sourceFiniteGapNLSHamiltonian (by simp) (by norm_num)
      ⟨higherSobolevSourceInclusion s (b j).val,(b j).property⟩ (hb j) (k+1)) atTop
      (𝓝 ((2:ℂ)^k * ∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n k
        (higherSobolevSourceInclusion s a.val))) := by
  have he (j : ℕ) : sourceFiniteGapNLSHamiltonian (by simp) (by norm_num)
      ⟨higherSobolevSourceInclusion s (b j).val,(b j).property⟩ (hb j) (k+1) =
      (2:ℂ)^k * ∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n k
        (higherSobolevSourceInclusion s (b j).val) := by
    have h := sourceFiniteGap_tsum_complexHigherActions_eq_hamiltonian (by simp) (by norm_num)
      ⟨higherSobolevSourceInclusion s (b j).val,(b j).property⟩ (hb j) k
    have hpow : (2:ℂ)^k ≠ 0 := pow_ne_zero _ (by norm_num)
    exact ((eq_div_iff hpow).mp h).symm.trans (mul_comm _ _)
  simp_rw [he]
  have hc := (analyticAt_tsum_sourceHigherSobolevHigherAction s a.val a.property k hk).continuousAt
  exact ((hc.comp continuous_subtype_val.continuousAt).tendsto.comp hlim).const_mul _

/-- One sequence approximates the original Hˢ source and simultaneously all
physical finite-gap Hamiltonians through order 2s+1 with the factor 2^k. -/
theorem exists_sourceHigherSobolevFiniteGapHamiltonian_approximation
    (a : realTypeHigherSobolevSourceLocus s) :
    ∃ b : ℕ → realTypeHigherSobolevSourceLocus s,
      ∃ hb : ∀ j, b j ∈ sourceHigherSobolevFiniteGapLocus s,
        Tendsto b atTop (𝓝 a) ∧ ∀ k : ℕ, k ≤ 2*s →
          Tendsto (fun j => sourceFiniteGapNLSHamiltonian (by simp) (by norm_num)
            ⟨higherSobolevSourceInclusion s (b j).val,(b j).property⟩ (hb j) (k+1)) atTop
            (𝓝 ((2:ℂ)^k * ∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n k
              (higherSobolevSourceInclusion s a.val))) := by
  obtain ⟨b,hb,hlim⟩ := exists_sourceHigherSobolevFiniteGap_sequence s a
  exact ⟨b,hb,hlim,fun k hk => tendsto_sourceHigherSobolevFiniteGapHamiltonian s a b hb hlim k hk⟩

end NLS.ZakharovShabat
