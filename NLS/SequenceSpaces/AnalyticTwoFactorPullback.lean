import NLS.SequenceSpaces.AnalyticTwoFactorRemainder

/-! Combine native first-factor data with a second exact analytic factor
on a rough source domain, preserving one common original neighborhood. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Coeff

theorem exists_two_factor_remainder_from_rough_data
    {E Q : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    (L : E →L[ℂ] Q) (V : Set E) (Z : Set Q) (q : E)
    (hV : IsOpen V) (hZ : IsOpen Z) (hqV : q∈V) (hqZ : L q∈Z)
    (P : Q → Coeff 2) (F : E → Coeff 2) (N₁ M₁ : E → Coeff ⊤) (N₂ M₂ : Q → Coeff ⊤)
    (phase₂ : ℕ+ → Q → ℂ) (Valid : Q → Prop)
    (CF CN₁ CM₁ CN₂ CM₂ : ℝ) (hCN₁ : 0≤CN₁) (hCM₁ : 0≤CM₁) (hCN₂ : 0≤CN₂) (hCM₂ : 0≤CM₂)
    (hFa : AnalyticOnNhd ℂ F V) (hN₁a : AnalyticOnNhd ℂ N₁ V) (hM₁a : AnalyticOnNhd ℂ M₁ V)
    (hN₂a : AnalyticOnNhd ℂ N₂ Z) (hM₂a : AnalyticOnNhd ℂ M₂ Z)
    (hdata : ∀ p∈V, Valid (L p) ∧ ‖F p‖≤CF ∧ ‖N₁ p‖≤CN₁ ∧ ‖M₁ p‖≤CM₁ ∧
      (∀ j : ℤ, F p j=(Weight.sobolev 1 j:ℂ)*P (L p) j) ∧
      ∀ j : ℤ, M₁ p j*N₁ p j*P (L p) j=
        (Weight.sobolev 1 j:ℂ)*(P (L p) j-N₁ p j*P (L p) j))
    (hP : ∀ p∈V, ∀ j : ℤ, j≤0 → P (L p) j=0)
    (hN₂b : ∀ a∈Z, ‖N₂ a‖≤CN₂) (hM₂b : ∀ a∈Z, ‖M₂ a‖≤CM₂)
    (hM₂c : ∀ a∈Z, ∀ n : ℕ+, M₂ a (n:ℤ)=(1+(n:ℂ))*(phase₂ n a-1))
    (hN₂c : ∀ a∈Z, ∀ n : ℕ+, phase₂ n a*N₂ a (n:ℤ)=1) :
    ∃ U : Set E, IsOpen U ∧ q∈U ∧ U⊆V ∧
      ∃ A : E → WeightedCoeff (Weight.sobolev 1) 2, ∃ R : E → WeightedCoeff (Weight.sobolev 2) 2,
        AnalyticOnNhd ℂ A U ∧ AnalyticOnNhd ℂ R U ∧ ∀ p∈U,
          L p∈Z ∧ Valid (L p) ∧ ‖A p‖≤CN₂*(CN₁*CF) ∧
          ‖R p‖≤CM₁*(CN₁*CF)+CM₂*(CN₂*(CN₁*CF)) ∧
          (∀ j : ℤ, (A p).val j=N₂ (L p) j*(N₁ p j*P (L p) j)) ∧
          ∀ j : ℤ, (R p).val j=P (L p) j-(A p).val j := by
  let U := V∩L ⁻¹' Z
  have hU : IsOpen U := hV.inter (hZ.preimage L.continuous)
  have hN₂a' : AnalyticOnNhd ℂ (fun p => N₂ (L p)) U :=
    fun p hp => (hN₂a (L p) hp.2).comp (L.analyticAt p)
  have hM₂a' : AnalyticOnNhd ℂ (fun p => M₂ (L p)) U :=
    fun p hp => (hM₂a (L p) hp.2).comp (L.analyticAt p)
  have hc₂ (p) (hp : p∈U) : ∀ j : ℤ,
      M₂ (L p) j*N₂ (L p) j*P (L p) j=
        (Weight.sobolev 1 j:ℂ)*(P (L p) j-N₂ (L p) j*P (L p) j) :=
    weighted_phase_compensation_of_positive (P (L p)) (N₂ (L p)) (M₂ (L p))
      (fun n => phase₂ n (L p)) (hP p hp.1) (hM₂c (L p) hp.2) (hN₂c (L p) hp.2)
  obtain ⟨A,R,hAa,hRa,hd⟩ := exists_analytic_weighted_two_factor_remainder U
    (fun p => P (L p)) F N₁ M₁ (fun p => N₂ (L p)) (fun p => M₂ (L p))
    CF CN₁ CM₁ CN₂ CM₂ hCN₁ hCM₁ hCN₂ hCM₂
    (fun p hp => hFa p hp.1) (fun p hp => hN₁a p hp.1) (fun p hp => hM₁a p hp.1) hN₂a' hM₂a'
    (fun p hp => (hdata p hp.1).2.1) (fun p hp => (hdata p hp.1).2.2.1)
    (fun p hp => (hdata p hp.1).2.2.2.1) (fun p hp => hN₂b (L p) hp.2) (fun p hp => hM₂b (L p) hp.2)
    (fun p hp => (hdata p hp.1).2.2.2.2.1) (fun p hp => (hdata p hp.1).2.2.2.2.2) hc₂
  refine ⟨U,hU,⟨hqV,hqZ⟩,inter_subset_left,A,R,hAa,hRa,?_⟩
  intro p hp
  exact ⟨hp.2,(hdata p hp.1).1,(hd p hp).1,(hd p hp).2.1,(hd p hp).2.2.1,(hd p hp).2.2.2⟩

end NLS.Coeff
