import NLS.KdV.PhysicalSharpFrequencyDecay
import NLS.KdV.PhysicalRenormalizedCorrectionAnalytic

/-! The FULL physical frequency bound pulls back through an actual
analytic inverse pair germ, preserving all complex sources at once. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {t : ℝ} {ht : 0≤t} {J : E →L[ℂ] PeriodOneHminusOne}

theorem PhysicalFrequencyParameterization.exists_pair_frequency_pullback
    (A : PhysicalFrequencyParameterization E t ht J)
    (P : F →L[ℂ] E) (Q : (Coeff 2 × Coeff 2) → F)
    (R : F →L[ℂ] PeriodOneHminusOne) (hR : ∀ a, J (P a)=R a)
    (U : Set (Coeff 2 × Coeff 2)) (hU : IsOpen U) (hQ : AnalyticOnNhd ℂ Q U)
    (z₀ : Coeff 2 × Coeff 2) (hz₀ : z₀∈U)
    (hqA : P (Q z₀)∈A.domain) (hqr : IsRealPeriodOneHminusOne (J (P (Q z₀))))
    (hs : A.HasSharpFrequencyDecay (P (Q z₀))) :
    ∃ B : PhysicalMiuraFrequencyChart, ∃ T : Set (Coeff 2 × Coeff 2),
      ∃ f : ℕ+ → (Coeff 2 × Coeff 2) → ℂ,
        IsOpen T ∧ z₀∈T ∧ T⊆U ∧ (∀ z∈T, R (Q z)∈B.domain) ∧
        (∀ n, AnalyticOnNhd ℂ (f n) T) ∧
        (∀ n, ∀ z∈T, f n z=B.correction n (R (Q z))+12*sourceComplexHigherAction
          (by norm_num) (by norm_num) (n:ℤ) 1 (hillMiuraDiagonal (B.psi.miura.lift (R (Q z))))) ∧
        ∃ K : ℕ, ∃ M : ℝ, 0≤M ∧
          (∀ z∈T, ∀ n : ℕ+, K≤(n:ℤ).natAbs → Weight.sobolev (3*t-1) (n:ℤ)*‖f n z‖≤M) ∧
          (t<2/3 → ∀ z∈T, Tendsto (fun n : ℕ => Weight.sobolev (3*t-1) ((n+1:ℕ):ℤ)*
            ‖f ⟨n+1,by omega⟩ z‖) atTop (𝓝 0)) := by
  obtain ⟨Ts,hTs,hqTs,hTsA,K,M,hM,hb,hd,_hphysical⟩ := hs
  obtain ⟨Ta,hTa,hqTa,_hTaA,ha⟩ := A.exists_analytic_renormalized_domain (P (Q z₀)) hqA hqr
  let S := Ts∩Ta
  let η := fun z => P (Q z)
  have hη : AnalyticOnNhd ℂ η U := fun z hz => (P.analyticAt _).comp (hQ z hz)
  let T := U∩η ⁻¹' S
  have hT : IsOpen T := hη.continuousOn.isOpen_inter_preimage hU (hTs.inter hTa)
  have hzT : z₀∈T := ⟨hz₀,hqTs,hqTa⟩
  let f := fun n z => A.renormalizedCorrection n (η z)
  refine ⟨A.physical,T,f,hT,hzT,inter_subset_left,?_,?_,?_,K,M,hM,?_,?_⟩
  · intro z hz
    have h := A.domain_subset (hTsA hz.2.1)
    change J (P (Q z))∈A.physical.domain at h
    rw [hR] at h
    exact h
  · intro n z hz
    exact (ha n (η z) hz.2.2).comp (hη z hz.1)
  · intro n z _hz
    dsimp only [f,η,PhysicalFrequencyParameterization.renormalizedCorrection]
    rw [hR]
  · intro z hz n hn
    exact hb (η z) hz.2.1 n hn
  · intro ht2 z hz
    exact hd ht2 (η z) hz.2.1

end NLS.KdV
