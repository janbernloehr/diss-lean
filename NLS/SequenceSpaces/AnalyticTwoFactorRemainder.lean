import NLS.SequenceSpaces.AnalyticWeightedPhaseRemainder
import NLS.SequenceSpaces.SobolevHomogeneous

/-! Two exact reciprocal factors can be removed successively, keeping
one full derivative in the SUM of their analytic packet remainders. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Coeff

theorem exists_analytic_weighted_two_factor_remainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Set E) (P F : E → Coeff 2) (N₁ M₁ N₂ M₂ : E → Coeff ⊤)
    (CF CN₁ CM₁ CN₂ CM₂ : ℝ) (hCN₁ : 0≤CN₁) (hCM₁ : 0≤CM₁) (hCN₂ : 0≤CN₂) (hCM₂ : 0≤CM₂)
    (hFa : AnalyticOnNhd ℂ F U) (hN₁a : AnalyticOnNhd ℂ N₁ U) (hM₁a : AnalyticOnNhd ℂ M₁ U)
    (hN₂a : AnalyticOnNhd ℂ N₂ U) (hM₂a : AnalyticOnNhd ℂ M₂ U)
    (hFb : ∀ p∈U, ‖F p‖≤CF) (hN₁b : ∀ p∈U, ‖N₁ p‖≤CN₁) (hM₁b : ∀ p∈U, ‖M₁ p‖≤CM₁)
    (hN₂b : ∀ p∈U, ‖N₂ p‖≤CN₂) (hM₂b : ∀ p∈U, ‖M₂ p‖≤CM₂)
    (hFc : ∀ p∈U, ∀ j : ℤ, F p j=(Weight.sobolev 1 j:ℂ)*P p j)
    (hc₁ : ∀ p∈U, ∀ j : ℤ, M₁ p j*N₁ p j*P p j=
      (Weight.sobolev 1 j:ℂ)*(P p j-N₁ p j*P p j))
    (hc₂ : ∀ p∈U, ∀ j : ℤ, M₂ p j*N₂ p j*P p j=
      (Weight.sobolev 1 j:ℂ)*(P p j-N₂ p j*P p j)) :
    ∃ A : E → WeightedCoeff (Weight.sobolev 1) 2, ∃ R : E → WeightedCoeff (Weight.sobolev 2) 2,
      AnalyticOnNhd ℂ A U ∧ AnalyticOnNhd ℂ R U ∧ ∀ p∈U,
        ‖A p‖≤CN₂*(CN₁*CF) ∧ ‖R p‖≤CM₁*(CN₁*CF)+CM₂*(CN₂*(CN₁*CF)) ∧
        (∀ j : ℤ, (A p).val j=N₂ p j*(N₁ p j*P p j)) ∧
        ∀ j : ℤ, (R p).val j=P p j-(A p).val j := by
  obtain ⟨A₁,R₁,hA₁a,hR₁a,h₁⟩ := exists_analytic_weighted_phase_remainder U P F N₁ M₁ CF CN₁ CM₁
    hCN₁ hCM₁ hFa hN₁a hM₁a hFb hN₁b hM₁b hFc hc₁
  let W := (WeightedCoeff.weightIsometry (Weight.sobolev 1) 2).toContinuousLinearEquiv.toContinuousLinearMap
  let F₁ := fun p => W (A₁ p)
  have hF₁a : AnalyticOnNhd ℂ F₁ U := fun p hp => (W.analyticAt _).comp (hA₁a p hp)
  have hF₁b (p) (hp : p∈U) : ‖F₁ p‖≤CN₁*CF :=
    ((WeightedCoeff.weightIsometry (Weight.sobolev 1) 2).norm_map (A₁ p)).le.trans (h₁ p hp).1
  have hF₁c (p) (_hp : p∈U) (j : ℤ) : F₁ p j=(Weight.sobolev 1 j:ℂ)*(A₁ p).val j := rfl
  have hc₂' (p) (hp : p∈U) (j : ℤ) : M₂ p j*N₂ p j*(A₁ p).val j=
      (Weight.sobolev 1 j:ℂ)*((A₁ p).val j-N₂ p j*(A₁ p).val j) := by
    rw [(h₁ p hp).2.2.1 j]
    linear_combination (norm := ring) N₁ p j*(hc₂ p hp j)
  obtain ⟨A₂,R₂,hA₂a,hR₂a,h₂⟩ := exists_analytic_weighted_phase_remainder U
    (fun p => WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) (A₁ p)) F₁ N₂ M₂
    (CN₁*CF) CN₂ CM₂ hCN₂ hCM₂ hF₁a hN₂a hM₂a hF₁b hN₂b hM₂b
    (fun p hp j => by simpa only [WeightedCoeff.sobolevToL2_apply] using hF₁c p hp j)
    (fun p hp j => by simpa only [WeightedCoeff.sobolevToL2_apply] using hc₂' p hp j)
  have hbase (p) (j : ℤ) :
      WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) (A₁ p) j=(A₁ p).val j := by
    simp only [WeightedCoeff.sobolevToL2_apply]
  refine ⟨A₂,(fun p => R₁ p+R₂ p),hA₂a,hR₁a.add hR₂a,?_⟩
  intro p hp
  refine ⟨(h₂ p hp).1,(norm_add_le _ _).trans (add_le_add (h₁ p hp).2.1 (h₂ p hp).2.1),?_,?_⟩
  · intro j
    rw [(h₂ p hp).2.2.1 j,hbase,(h₁ p hp).2.2.1 j]
  · intro j
    rw [WeightedCoeff.add_val,(h₁ p hp).2.2.2 j,(h₂ p hp).2.2.2 j,hbase]
    ring

end NLS.Coeff
