import NLS.SequenceSpaces.CompactUniformFrequencyBounds
import NLS.SequenceSpaces.CompactSobolevInclusion

/-! An opaque source model turns compact corrected-frequency bounds and
an exact quadratic action estimate into uniform bounds on bounded sets. -/
noncomputable section
open Set Metric
namespace NLS.Coeff

theorem exists_bounded_frequency_bound_of_compact_corrected
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F] [T2Space F]
    (J : E →L[ℝ] F) (hJ : IsCompactOperator J)
    (d I₀ : ℕ+ → E → ℂ) (g : ℕ+ → F → ℂ) (w : ℤ → ℝ)
    (hw : ∀ n : ℕ+, (n:ℝ)≤w (n:ℤ))
    (he : ∀ q n, g n (J q)=d n q+6*I₀ n q)
    (hc : ∀ K : Set F, IsCompact K → ∃ M : ℝ, 0≤M ∧
      ∀ a∈K, ∀ n : ℕ+, w (n:ℤ)*‖g n a‖≤M)
    (hI : ∀ q (n : ℕ+), w (n:ℤ)*‖I₀ n q‖≤‖q‖^2)
    (S : Set E) (hS : Bornology.IsBounded S) :
    ∃ B : ℝ, 0≤B ∧ ∀ q∈S, ∀ n : ℕ+, (n:ℝ)*‖d n q‖≤B := by
  obtain ⟨R₀,hR₀⟩ := hS.exists_norm_le
  let R := max R₀ 0
  have hR : 0≤R := le_max_right _ _
  let K := closure (J '' closedBall (0 : E) R)
  have hK : IsCompact K := hJ.isCompact_closure_image_of_bounded isBounded_closedBall
  obtain ⟨M,hM,hcorr⟩ := hc K hK
  refine ⟨M+6*R^2,by positivity,?_⟩
  intro q hq n
  have hqR : ‖q‖≤R := (hR₀ q hq).trans (le_max_left _ _)
  have hqK : J q∈K := subset_closure ⟨q,by rwa [mem_closedBall_zero_iff],rfl⟩
  have hcg := hcorr (J q) hqK n
  rw [he] at hcg
  have hi : w (n:ℤ)*‖I₀ n q‖≤R^2 := (hI q n).trans ((sq_le_sq₀ (norm_nonneg _) hR).mpr hqR)
  have hwp : 0≤w (n:ℤ) := (show (0:ℝ)≤n by positivity).trans (hw n)
  have hd := mul_le_mul_of_nonneg_left (norm_sub_le (d n q+6*I₀ n q) (6*I₀ n q)) hwp
  rw [add_sub_cancel_right,norm_mul,Complex.norm_ofNat,mul_add] at hd
  have hlow := mul_le_mul_of_nonneg_right (hw n) (norm_nonneg (d n q))
  nlinarith

theorem exists_bounded_frequency_bound_isometry
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (f : ℕ+ → F → ℂ) (d : ℕ+ → E → ℂ)
    (he : ∀ n q, f n (e q)=d n q)
    (hb : ∀ T : Set F, Bornology.IsBounded T → ∃ B : ℝ, 0≤B ∧
      ∀ a∈T, ∀ n : ℕ+, (n:ℝ)*‖f n a‖≤B)
    (S : Set E) (hS : Bornology.IsBounded S) :
    ∃ B : ℝ, 0≤B ∧ ∀ q∈S, ∀ n : ℕ+, (n:ℝ)*‖d n q‖≤B := by
  have hT : Bornology.IsBounded (e '' S) := e.isometry.lipschitz.isBounded_image hS
  obtain ⟨B,hB,hall⟩ := hb (e '' S) hT
  refine ⟨B,hB,?_⟩
  intro q hq n
  simpa only [he] using hall (e q) ⟨q,hq,rfl⟩ n

end NLS.Coeff
