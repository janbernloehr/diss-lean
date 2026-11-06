import NLS.KdV.HillHminusOneUniformAnnularRoot
import NLS.KdV.FreeEnergyCircleFrequencyBounds
import NLS.ComplexAnalysis.SquaredDiscNormBound
import NLS.ComplexAnalysis.AnalyticLinearSourcePullback
/-! # Native Hilbert numerator and density bounds on free energy discs

Maximum modulus transfers the complete Hilbert norm from squared frequency
circles. Uniform actual annular root separation then gives density decay
on radius-k energy circles on one complex period-one L2 ball.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_uniform_energy_density_bound_of_frequency_family
    (η : ℝ) (hη : 0 < η) (F : ℂ × Coeff 2 → Coeff 2)
    (hF : AnalyticOnNhd ℂ F (univ ×ˢ ball (0 : Coeff 2) η))
    (K : ℝ) (hK : 0 < K)
    (hfreq : ∀ u ∈ ball (0 : Coeff 2) η, ∀ k : ℕ+,
      ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/8),
        (z^2,periodOneL2Inclusion u) ∈ hillHminusContinuationDomain ∧
        ‖(hillHminusContinuedRoot (z^2,periodOneL2Inclusion u))⁻¹ • F (z^2,u)‖ ≤ K/(k : ℝ)) :
    ∃ θ : ℝ, 0 < θ ∧ ball (0 : Coeff 2) θ ⊆ ball (0 : Coeff 2) η ∧
      ∃ C : ℝ, 0 < C ∧ ∀ u ∈ ball (0 : Coeff 2) θ, ∀ k : ℕ+,
        (∀ E ∈ closedBall (freeHillEnergy k) (k : ℝ), ‖F (E,u)‖ ≤ C/(k : ℝ)) ∧
        ∀ E ∈ sphere (freeHillEnergy k) (k : ℝ),
          (E,periodOneL2Inclusion u) ∈ hillHminusContinuationDomain ∧
          ‖(hillHminusContinuedRoot (E,periodOneL2Inclusion u))⁻¹ • F (E,u)‖ ≤ C/(k : ℝ) := by
  have hr : 0 < 1/(4*Real.pi) := by positivity
  have hrpi : 1/(4*Real.pi) ≤ Real.pi/4 := by
    apply (div_le_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    nlinarith [Real.pi_gt_three]
  obtain ⟨δ,b,hδ,hb,htrace,hroot⟩ := exists_hillHminus_uniform_annular_root_bound _ hr hrpi
  obtain ⟨θ,hθ,hs⟩ := exists_common_ball_linear_preimage periodOneL2Inclusion δ (η/2)
    hδ (by positivity) univ isOpen_univ (mem_univ _)
  have hsub : ball (0 : Coeff 2) θ ⊆ ball (0 : Coeff 2) η := by
    intro u hu
    rw [mem_ball_zero_iff]
    exact ((hs u hu).2.2).trans_lt (by linarith)
  let M := 1+2*Real.exp (Real.pi/4)+2
  let D := M*K
  have hM : 0 < M := by dsimp only [M];positivity
  have hD : 0 < D := mul_pos hM hK
  refine ⟨θ,hθ,hsub,max D (D/b),lt_of_lt_of_le hD (le_max_left _ _),?_⟩
  intro u hu k
  have huη := hsub hu
  have hqδ := (hs u hu).1
  have hFe : Differentiable ℂ (fun E : ℂ => F (E,u)) := by
    intro E
    exact ((hF (E,u) ⟨mem_univ _,huη⟩).comp
      (f := fun z : ℂ => (z,u)) (analyticAt_id.prod analyticAt_const)).differentiableAt
  have houter (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/8)) :
      ‖F (z^2,u)‖ ≤ D/(k : ℝ) := by
    obtain ⟨ht,hf⟩ := hfreq u huη k z hz
    have hzq : z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) :=
      closedBall_subset_closedBall (by linarith [Real.pi_pos]) (sphere_subset_closedBall hz)
    have hR := norm_hillHminusContinuedRoot_le_of_trace_bound _ ht _
      (by positivity : 0 ≤ 1+2*Real.exp (Real.pi/4)) (htrace _ hqδ k z hzq)
    have hn : hillHminusContinuedRoot (z^2,periodOneL2Inclusion u) ≠ 0 :=
      hillHminusSourceFamily.root_ne_zero _ ht
    have he : F (z^2,u) = hillHminusContinuedRoot (z^2,periodOneL2Inclusion u) •
        ((hillHminusContinuedRoot (z^2,periodOneL2Inclusion u))⁻¹ • F (z^2,u)) := by
      rw [smul_smul,mul_inv_cancel₀ hn,one_smul]
    rw [he,norm_smul]
    exact (mul_le_mul hR hf (norm_nonneg _) hM.le).trans_eq (by dsimp only [D];ring)
  have hboundary (E : ℂ) (hE : E ∈ sphere (freeHillEnergy k) (k : ℝ)) : ‖F (E,u)‖ ≤ D/(k : ℝ) :=
    norm_le_of_squared_frequency_sphere_bound (fun E => F (E,u)) hFe _ _ _
      (by positivity) houter E (hillFreeEnergyCircle_frequency_bounds k E hE).1
  have hdisc (E : ℂ) (hE : E ∈ closedBall (freeHillEnergy k) (k : ℝ)) : ‖F (E,u)‖ ≤ D/(k : ℝ) := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le
      (isBounded_ball (x := freeHillEnergy k) (r := (k : ℝ))) hFe.diffContOnCl
    · intro z hz
      rw [frontier_ball _ (by positivity : (k : ℝ) ≠ 0)] at hz
      exact hboundary z hz
    · rw [closure_ball (freeHillEnergy k) (by positivity : (k : ℝ) ≠ 0)]
      exact hE
  refine ⟨fun E hE => (hdisc E hE).trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)),?_⟩
  intro E hE
  obtain ⟨hz,hfar⟩ := hillFreeEnergyCircle_frequency_bounds k E hE
  have hzq := closedBall_subset_closedBall (by linarith [Real.pi_pos] : Real.pi/8 ≤ Real.pi/4) hz
  obtain ⟨ht,hR⟩ := hroot _ hqδ k (sqrt E) hzq hfar
  rw [sq_sqrt] at ht hR
  refine ⟨ht,?_⟩
  rw [norm_smul,norm_inv,← div_eq_inv_mul]
  calc
    _ ≤ (D/(k : ℝ))/b := div_le_div₀ (by positivity) (hboundary E hE) hb hR
    _ = (D/b)/(k : ℝ) := by ring
    _ ≤ max D (D/b)/(k : ℝ) := div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)
end NLS.KdV
