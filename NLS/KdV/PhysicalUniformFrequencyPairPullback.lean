import NLS.KdV.PhysicalUniformFrequencyDecay
import NLS.KdV.PhysicalRenormalizedCorrectionAnalytic

/-! A fixed complex inverse-pair neighborhood carries the full actual
uniform frequency tail, in the same physical chart at every label. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {t : ℝ} {ht : 0≤t} {J : E →L[ℂ] PeriodOneHminusOne}

theorem PhysicalFrequencyParameterization.exists_uniform_pair_frequency_pullback
    (A : PhysicalFrequencyParameterization E t ht J) (ht0 : 0<t) (ht1 : t<2/3)
    (Q : (Coeff 2 × Coeff 2) → E) (U : Set (Coeff 2 × Coeff 2))
    (hU : IsOpen U) (hQ : AnalyticOnNhd ℂ Q U)
    (z₀ : Coeff 2 × Coeff 2) (hz₀ : z₀∈U) (hqA : Q z₀∈A.domain)
    (hqr : IsRealPeriodOneHminusOne (J (Q z₀))) :
    ∃ T : Set (Coeff 2 × Coeff 2), ∃ f : ℕ+ → (Coeff 2 × Coeff 2) → ℂ,
      IsOpen T ∧ z₀∈T ∧ T⊆U ∧ (∀ z∈T, J (Q z)∈A.physical.domain) ∧
      (∀ n, AnalyticOnNhd ℂ (f n) T) ∧
      (∀ n, ∀ z∈T, f n z=A.physical.correction n (J (Q z))+12*sourceComplexHigherAction
        (by norm_num) (by norm_num) (n:ℤ) 1 (hillMiuraDiagonal (A.physical.psi.miura.lift (J (Q z))))) ∧
      ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ z∈T, ∀ n : ℕ+, K≤(n:ℤ).natAbs →
        Weight.sobolev (3*t-1) (n:ℤ)*‖f n z‖≤ε := by
  obtain ⟨Ts,hTs,hqTs,hTsA,hb⟩ := A.exists_uniform_renormalized_frequency_decay ht0 ht1 (Q z₀) hqA hqr
  obtain ⟨Ta,hTa,hqTa,_,ha⟩ := A.exists_analytic_renormalized_domain (Q z₀) hqA hqr
  let T := U∩Q ⁻¹' (Ts∩Ta)
  have hT : IsOpen T := hQ.continuousOn.isOpen_inter_preimage hU (hTs.inter hTa)
  let f := fun n z => A.renormalizedCorrection n (Q z)
  refine ⟨T,f,hT,⟨hz₀,hqTs,hqTa⟩,inter_subset_left,
    (fun z hz => A.domain_subset (hTsA hz.2.1)),?_,?_,?_⟩
  · intro n z hz
    exact (ha n (Q z) hz.2.2).comp (hQ z hz.1)
  · intro n z _
    rfl
  · intro ε hε
    obtain ⟨K,hK⟩ := hb ε hε
    exact ⟨K,fun z hz n hn => hK (Q z) hz.2.1 n hn⟩

end NLS.KdV
