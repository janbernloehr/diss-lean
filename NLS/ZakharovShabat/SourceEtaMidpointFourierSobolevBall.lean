import NLS.ZakharovShabat.SourceEtaMidpointFourierSobolevBallSmooth
import NLS.ZakharovShabat.SourceEtaMidpointFourierContinuity
import NLS.ZakharovShabat.SobolevSourceRealSmoothApproximation

/-! # Complete midpoint Fourier bounds on real Sobolev balls

Smooth approximation and compact finite heads give a uniform one-order stronger bound for the full canonical midpoint remainder.
-/

noncomputable section
open Set Metric Filter Topology Complex NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The uniform midpoint Fourier tail bound extends to every real source
in the original Sobolev ball, without smooth representative assumptions. -/
theorem exists_uniform_real_source_eta_midpoint_fourier_tail_bound
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab : realTypeHigherSobolevSourceLocus s, ‖ab.val‖ ≤ R →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K ≤ n.natAbs then
          sourceEtaMidpointFourierError (by simp) (by norm_num) (higherSobolevSourceInclusion s ab.val) n
          else 0) ∧ ‖f‖ ≤ C := by
  classical
  obtain ⟨K,hK,C,hC,hbound⟩ := exists_uniform_real_source_eta_midpoint_smooth_fourier_tail_bound s hs R hR
  refine ⟨K,hK,C,hC,?_⟩
  intro ab hab
  let u (N : ℕ) : realTypeHigherSobolevSourceLocus s :=
    ⟨sobolevSourceSymmetricTruncate s N ab.val,sobolevSourceSymmetricTruncate_real s N ab⟩
  have hu (N : ℕ) : ‖(u N).val‖ ≤ R := (norm_sobolevSourceSymmetricTruncate_le s N ab.val).trans hab
  have he (N : ℕ) : ∃ e : ScalarSobolev (s+1),
      (∀ n, e.val n = if K ≤ n.natAbs then
        sourceEtaMidpointFourierError (by simp) (by norm_num) (higherSobolevSourceInclusion s (u N).val) n
        else 0) ∧ ‖e‖ ≤ C := by
    obtain ⟨a,b,ha,hb,hpa,hpb,hca,hcb⟩ := sobolevSourceSymmetricTruncate_smooth s N ab.val
    exact hbound (u N) (hu N) a b ha hb hpa hpb hca hcb
  choose e he hen using he
  refine WeightedCoeff.exists_of_bounded_coefficientwise_tendsto (l := (atTop : Filter ℕ))
    (Weight.sobolev ((s+1:ℕ):ℝ)) e _ C hen ?_
  intro n
  simp only [he]
  by_cases hn : K ≤ n.natAbs
  · simp only [if_pos hn]
    exact Filter.Tendsto.comp
      (continuousAt_sourceEtaMidpointFourierError_of_real
        ⟨higherSobolevSourceInclusion s ab.val,ab.property⟩ n)
      (((higherSobolevSourceInclusion s).continuous.tendsto ab.val).comp
        (tendsto_sobolevSourceSymmetricTruncate s ab.val))
  · simp only [if_neg hn]
    exact tendsto_const_nhds

/-- Finite-head compactness completes the uniform midpoint Fourier bound
at every signed index on the whole real Sobolev ball. -/
theorem exists_uniform_real_source_eta_midpoint_fourier_bound
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : realTypeHigherSobolevSourceLocus s, ‖ab.val‖ ≤ R →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = sourceEtaMidpointFourierError (by simp) (by norm_num)
          (higherSobolevSourceInclusion s ab.val) n) ∧ ‖f‖ ≤ C := by
  classical
  obtain ⟨N,_,C,hC,htail⟩ := exists_uniform_real_source_eta_midpoint_fourier_tail_bound s hs R hR
  let J := higherSobolevSourceInclusion s
  let X := closedBall (0 : SobolevSource s) R ∩ (J ⁻¹' realTypeSourceLocus 2)
  let K := closure (J '' X)
  obtain ⟨hK,hKreal⟩ := higherSobolev_real_ball_image_compact s hs R
  let w := Weight.sobolev ((s+1:ℕ):ℝ)
  obtain ⟨B,hB,hhead⟩ := exists_sourceEtaMidpointFourierHead_bound_on_compact w (Coeff.lowFrequencies N) K hK hKreal
  refine ⟨C+B,by positivity,?_⟩
  intro ab hab
  have hmem : J ab.val ∈ K := subset_closure ⟨ab.val,
    ⟨by simpa only [mem_closedBall,dist_zero_right] using hab,ab.property⟩,rfl⟩
  obtain ⟨e,he,hen⟩ := htail ab hab
  let H : ScalarSobolev (s+1) := WeightedCoeff.finiteBlock w (Coeff.lowFrequencies N)
    (fun n => sourceEtaMidpointFourierError (by simp) (by norm_num) (J ab.val) n)
  refine ⟨e+H,?_,(norm_add_le e H).trans (add_le_add hen (hhead (J ab.val) hmem))⟩
  intro n
  simp only [WeightedCoeff.add_val,he,H,WeightedCoeff.finiteBlock_val,Coeff.mem_lowFrequencies]
  by_cases hn : N ≤ n.natAbs
  · simp only [if_pos hn,if_neg (not_lt_of_ge hn),add_zero,J]
  · simp only [if_neg hn,if_pos (Nat.lt_of_not_ge hn),zero_add,J]

/-- The canonical complete midpoint Fourier remainder maps every real
original Hs ball to a bounded subset of h^(s+1). -/
theorem exists_uniform_real_sourceEtaMidpointFourierRemainder_bound
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : realTypeHigherSobolevSourceLocus s, ‖ab.val‖ ≤ R →
      ‖sourceEtaMidpointFourierRemainder s ab.val‖ ≤ C ∧
      ∀ n, (sourceEtaMidpointFourierRemainder s ab.val).val n =
        sourceEtaMidpointFourierError (by simp) (by norm_num) (higherSobolevSourceInclusion s ab.val) n := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_real_source_eta_midpoint_fourier_bound s hs R hR
  refine ⟨C,hC,?_⟩
  intro ab hab
  obtain ⟨e,he,hen⟩ := hbound ab hab
  let e' : WeightedCoeff (Weight.sobolev ((s:ℝ)+1)) 2 :=
    WeightedCoeff.sobolevInclusion (by norm_num : (s:ℝ)+1 ≤ ((s+1:ℕ):ℝ)) e
  have he' : sourceEtaMidpointFourierRemainder s ab.val = e' := by
    apply WeightedCoeff.ofFunctionOrZero_eq_of_coordinates
    intro n
    simpa only [e',WeightedCoeff.sobolevInclusion_apply] using he n
  rw [he']
  exact ⟨(WeightedCoeff.norm_sobolevInclusion_le _ e).trans hen,
    fun n => by simpa only [e',WeightedCoeff.sobolevInclusion_apply] using he n⟩

end NLS.ZakharovShabat
