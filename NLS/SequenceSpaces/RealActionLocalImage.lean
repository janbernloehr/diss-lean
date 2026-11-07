import NLS.SequenceSpaces.RealActionLifting

/-! A continuous actual inverse of real Birkhoff pairs realizes a full
relative action neighborhood in every open source neighborhood. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Coeff

theorem exists_real_action_ball_in_source_image
    {E : Type*} [TopologicalSpace E]
    (A : E → Coeff 1) (R : {z : Coeff 2 × Coeff 2 // z∈realPairLocus 2} → E)
    (hR : Continuous R) (he : ∀ z, A (R z)=quadraticActionsExponent (q := 1) z.val)
    (z₀ : {z : Coeff 2 × Coeff 2 // z∈realPairLocus 2})
    (T : Set E) (hT : IsOpen T) (hzT : R z₀∈T) :
    ∃ r : ℝ, 0<r ∧ ball (A (R z₀)) r∩nonnegativeLocus 1⊆A '' T := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (hT.preimage hR) z₀ hzT
  refine ⟨r^2/2,by positivity,?_⟩
  intro b hb
  obtain ⟨w,hwr,hw,hd⟩ := exists_nearby_real_quadraticActions (p := 2) (q := 1)
    (by norm_num) z₀.val z₀.property b hb.2
  have hb' : ‖b-quadraticActionsExponent (q := 1) z₀.val‖<r^2/2 := by
    simpa only [mem_ball,dist_eq_norm,he] using hb.1
  have hn : ‖w-z₀.val‖<r := (sq_lt_sq₀ (norm_nonneg _) hr.le).mp (by linarith)
  have hwball : (⟨w,hwr⟩ : {z : Coeff 2 × Coeff 2 // z∈realPairLocus 2})∈ball z₀ r := by
    change dist w z₀.val<r
    simpa only [dist_eq_norm] using hn
  exact ⟨R ⟨w,hwr⟩,hball hwball,(he ⟨w,hwr⟩).trans hw⟩

end NLS.Coeff
