import NLS.ZakharovShabat.RestoredSpectralPairs
import NLS.ZakharovShabat.FreeHalfDiscGeometry
import NLS.ComplexAnalysis.DiscBounds

/-!
# Common lp bounds for entire paired products and their derivatives

The off-lattice estimates hold on every half-pi boundary circle. Maximum
modulus extends the same lp majorant through all free centers. Cauchy then
controls derivatives on the quarter-pi discs, uniformly over norm balls of
both complete displacement sequences.
-/

noncomputable section
open scoped ENNReal
open Set Metric
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The entire paired product error from its correctly normalized free product. -/
def spectralPairError (a b : Coeff p) (z : ℂ) : ℂ :=
  entireSpectralPairProduct (displacedRoots a) (displacedRoots b) z-((freeDiscriminant z)^2-4)

/-- The paired product error is entire, including at every free center. -/
theorem differentiable_spectralPairError (hp : p ≠ ⊤) (a b : Coeff p) :
    Differentiable ℂ (spectralPairError a b) := by
  have h := (analyticOnNhd_entireSpectralPairProduct hp _ _ (memℓp_displacedRoots a)
    (memℓp_displacedRoots b)).differentiableOn
  have hf : Differentiable ℂ (fun z => (freeDiscriminant z)^2-4) := by unfold freeDiscriminant; fun_prop
  exact (differentiableOn_univ.mp h).sub hf

/-- Boundary bounds from the restored factors extend through the entire closed free disc. -/
theorem norm_spectralPairError_le_on_disc (hp : p ≠ ⊤) (a b A B : Coeff p)
    {C : ℝ} (hC : 0 ≤ C)
    (hs : ∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 → ‖Complex.sin z‖ ≤ C)
    (ha : ∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 →
      ‖restoredSineProduct a n z-Complex.sin z‖ ≤ ‖A n‖)
    (hb : ∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 →
      ‖restoredSineProduct b n z-Complex.sin z‖ ≤ ‖B n‖)
    (n : ℤ) (z : ℂ) (hz : ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2) :
    ‖spectralPairError a b z‖ ≤ ‖spectralPairErrorMajorant C A B n‖ := by
  apply NLS.ComplexAnalysis.norm_le_of_sphere_bound (differentiable_spectralPairError hp a b)
    ((Real.pi : ℂ)*n) (half_pos Real.pi_pos) _ _ hz
  intro w hw
  have hwd : ‖w-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 :=
    (show ‖w-(Real.pi : ℂ)*n‖ = Real.pi/2 by simpa only [mem_sphere, dist_eq_norm] using hw).le
  exact norm_entireSpectralPairProduct_sub_free_le_offLattice hp a b A B hC n w
    (freeHalfSphere_notMem_freeLattice n hw) (hs n w hwd) (ha n w hwd) (hb n w hwd)

/-- One value majorant controls the derivative on all the smaller source discs. -/
theorem norm_deriv_spectralPairError_le_on_disc (hp : p ≠ ⊤) (a b A : Coeff p)
    (hA : ∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 → ‖spectralPairError a b z‖ ≤ ‖A n‖)
    (n : ℤ) (z : ℂ) (hz : ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) :
    ‖deriv (spectralPairError a b) z‖ ≤ (4/Real.pi)*‖A n‖ := by
  have h := NLS.ComplexAnalysis.norm_deriv_le_of_closedDisc_bound (differentiable_spectralPairError hp a b)
    ((Real.pi : ℂ)*n) (by linarith [Real.pi_pos] : Real.pi/4 < Real.pi/2) _ (hA n) hz
  convert h using 1
  ring

/-- Both value and derivative bounds use one lp majorant, uniformly on a displacement norm ball. -/
theorem exists_uniform_spectralPairError_majorants (hp1 : 1 < p) (hp : p ≠ ⊤)
    {R : ℝ} (hR : 0 ≤ R) : ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : Coeff p, ‖a‖ ≤ R → ‖b‖ ≤ R →
      ∃ A : Coeff p, ‖A‖ ≤ K ∧
        (∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 → ‖spectralPairError a b z‖ ≤ ‖A n‖) ∧
        (∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 →
          ‖deriv (spectralPairError a b) z‖ ≤ (4/Real.pi)*‖A n‖) := by
  obtain ⟨K, hK, hbound⟩ := exists_uniform_restoredSineProduct_majorants hp1 hp hR
  obtain ⟨S, hS, hquot⟩ := exists_bound_freeSineQuotient (Real.pi/2)
  let C := S*(Real.pi/2)
  have hC : 0 ≤ C := mul_nonneg hS (half_pos Real.pi_pos).le
  have hs (n : ℤ) (z : ℂ) (hz : ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2) : ‖Complex.sin z‖ ≤ C := by
    rw [← freeSineQuotient_mul_sub n z, norm_mul]
    exact mul_le_mul (hquot n z hz) hz (norm_nonneg _) hS
  refine ⟨4*((C+K)*K+C*K), by positivity, fun a b ha hb => ?_⟩
  obtain ⟨A, hA, hvalA⟩ := hbound a ha
  obtain ⟨B, hB, hvalB⟩ := hbound b hb
  have hval := norm_spectralPairError_le_on_disc hp a b A B hC hs hvalA hvalB
  refine ⟨spectralPairErrorMajorant C A B, ?_, hval,
    norm_deriv_spectralPairError_le_on_disc hp a b _ hval⟩
  apply (norm_spectralPairErrorMajorant_le hC A B).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact add_le_add (mul_le_mul (add_le_add le_rfl hB) hA (norm_nonneg _) (add_nonneg hC hK))
    (mul_le_mul_of_nonneg_left hB hC)

/-- Arbitrary samples in the half-pi free discs give lp paired-product errors. -/
theorem memℓp_spectralPairError (hp1 : 1 < p) (hp : p ≠ ⊤) (a b : Coeff p)
    (z : ℤ → ℂ) (hz : ∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/2) :
    Memℓp (fun n => spectralPairError a b (z n)) p := by
  obtain ⟨_, _, h⟩ := exists_uniform_spectralPairError_majorants hp1 hp (norm_nonneg a |>.trans (le_max_left ‖a‖ ‖b‖))
  obtain ⟨A, _, hv, _⟩ := h a b (le_max_left _ _) (le_max_right _ _)
  exact (lp.memℓp A).mono' (fun n => hv n (z n) (hz n))

/-- Arbitrary samples in the quarter-pi free discs give lp derivative errors. -/
theorem memℓp_deriv_spectralPairError (hp1 : 1 < p) (hp : p ≠ ⊤) (a b : Coeff p)
    (z : ℤ → ℂ) (hz : ∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) :
    Memℓp (fun n => deriv (spectralPairError a b) (z n)) p := by
  obtain ⟨_, _, h⟩ := exists_uniform_spectralPairError_majorants hp1 hp (norm_nonneg a |>.trans (le_max_left ‖a‖ ‖b‖))
  obtain ⟨A, _, _, hd⟩ := h a b (le_max_left _ _) (le_max_right _ _)
  apply (lp.memℓp (((4/Real.pi : ℝ) : ℂ) • A)).mono'
  intro n
  simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity : 0 ≤ 4/Real.pi)] using hd n (z n) (hz n)

end NLS.ZakharovShabat
