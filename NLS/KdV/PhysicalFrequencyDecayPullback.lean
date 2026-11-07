import NLS.KdV.PhysicalSharpFrequencyDecay

/-! Pulling the full inverse-index bound back along an exact source
inclusion preserves the original parameter norm and physical chart. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {t : ℝ} {ht : 0≤t} {J : E →L[ℂ] PeriodOneHminusOne}

theorem PhysicalFrequencyParameterization.exists_inverse_index_decay_of_pullback
    (A : PhysicalFrequencyParameterization E t ht J)
    (P : F →L[ℂ] E) (Q : F →L[ℂ] PeriodOneHminusOne) (hQ : ∀ a, J (P a)=Q a)
    (q : F) (hs : A.HasSharpFrequencyDecay (P q)) (he : 3*t-1=1) :
    ∃ B : PhysicalMiuraFrequencyChart, ∃ T : Set F,
      IsOpen T ∧ q∈T ∧ T⊆Q ⁻¹' B.domain ∧ ∃ K : ℕ, ∃ M : ℝ, 0≤M ∧
        ∀ a∈T, ∀ n : ℕ+, K≤(n:ℤ).natAbs →
          (Weight.sobolev 1 (n:ℤ)*‖B.correction n (Q a)+
            12*sourceComplexHigherAction (by norm_num) (by norm_num) (n:ℤ) 1
              (hillMiuraDiagonal (B.psi.miura.lift (Q a)))‖≤M) ∧
          ∀ p : RealPeriodOneHillPotential, Q a=hillOriginalHminusSource p.val →
            Weight.sobolev 1 (n:ℤ)*‖B.correction n (hillOriginalHminusSource p.val)+
              6*(hillRealGapIntegral p.val p.property.1 p.property.2 (n:ℕ) 0 : ℂ)‖≤M := by
  obtain ⟨U,hU,hqU,hUA,K,M,hM,hb,_hd,hphysical⟩ := hs
  let T := P ⁻¹' U
  have hTB : T⊆Q ⁻¹' A.physical.domain := by
    intro a ha
    have h := A.domain_subset (hUA ha)
    change J (P a)∈A.physical.domain at h
    rw [hQ] at h
    exact h
  refine ⟨A.physical,T,hU.preimage P.continuous,hqU,hTB,K,M,hM,?_⟩
  intro a ha n hn
  constructor
  · have h := hb (P a) ha n hn
    rw [PhysicalFrequencyParameterization.renormalizedCorrection,hQ,he] at h
    exact h
  · intro p hp
    have h := (hphysical (P a) ha p ((hQ a).trans hp)).1 n hn
    rw [he] at h
    exact h

end NLS.KdV
