import NLS.ZakharovShabat.SourceAngularBetaH1Decay
import NLS.ZakharovShabat.SourceBirkhoffMapAnalytic
import NLS.ZakharovShabat.SourceAngularRealCharts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # H1 phase decay for the original Birkhoff family

The actual beta corrections and their signed exponential errors have
locally uniform inverse-bracket decay at real H1 sources. In particular,
they belong to every sequence exponent above one, including infinity.
Multiplication by the phase error gains one Sobolev derivative at any
real sequence order, with a locally uniform operator bound. This is one
ingredient of the full Birkhoff-minus-Fourier one-smoothing statement;
that full statement is not asserted here.
-/

noncomputable section
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
open Set Metric Complex Filter Topology
open scoped ENNReal
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- The actual real beta phase has its sharp elementary Lipschitz bound, for every real multiplier. -/
theorem norm_betaPhase_sub_one_le (φ : realTypeSourceSubmodule 2) (n : ℤ) (t : ℝ) :
    ‖exp ((t:ℂ)*I*sourceAngularBetaCorrection (by simp) (by norm_num) n s φ.val)-1‖ ≤
      |t| *‖sourceAngularBetaCorrection (by simp) (by norm_num) n s φ.val‖ := by
  let β := sourceAngularBetaCorrection (by simp) (by norm_num) n s φ.val
  have him := D.angular.correction_im_eq_zero_of_realType W D.source_open D.source_subset
    φ.val (D.real_subset φ.property) φ.property n
  have he : β = (β.re:ℂ) := Complex.ext rfl (by simpa only [ofReal_im] using him)
  change ‖exp ((t:ℂ)*I*β)-1‖ ≤ |t| *‖β‖
  rw [he]
  have hexp : (t:ℂ)*I*(β.re:ℂ) = I*((t*β.re:ℝ):ℂ) := by push_cast; ring
  rw [hexp]
  exact (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t*β.re)).trans (by
    rw [norm_mul,Real.norm_eq_abs,Complex.norm_real])

/-- One original family has locally uniform H1 decay of beta and both signed phase errors. -/
theorem exists_local_uniform_H1_beta_phase_decay (a : realTypeSobolevSourceLocus) :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧ a.val ∈ U ∧
      (∀ b ∈ U, sobolevSourceInclusion b ∈ W) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ b : realTypeSobolevSourceLocus, b.val ∈ U → ∀ n : ℤ,
        (1+|(n:ℝ)|)*‖sourceAngularBetaCorrection (by simp) (by norm_num) n s (sobolevSourceInclusion b.val)‖ ≤ K ∧
        ∀ t : ℝ, (1+|(n:ℝ)|)*‖exp ((t:ℂ)*I*
          sourceAngularBetaCorrection (by simp) (by norm_num) n s (sobolevSourceInclusion b.val))-1‖ ≤ |t| *K := by
  obtain ⟨V,hV,haV,_,K,hK,hβ⟩ := D.angular.exists_local_uniform_betaCorrection_H1_decay a
    (D.source_subset (D.real_subset a.property))
  refine ⟨V ∩ sobolevSourceInclusion ⁻¹' W,hV.inter (D.source_open.preimage sobolevSourceInclusion.continuous),
    ⟨haV,D.real_subset a.property⟩,(fun b hb => hb.2),K,hK,?_⟩
  intro b hb n
  refine ⟨hβ b hb.1 n,fun t => ?_⟩
  have hphase := D.norm_betaPhase_sub_one_le ⟨sobolevSourceInclusion b.val,b.property⟩ n t
  calc
    _ ≤ (1+|(n:ℝ)|)*(|t| *‖sourceAngularBetaCorrection (by simp) (by norm_num) n s
        (sobolevSourceInclusion b.val)‖) := mul_le_mul_of_nonneg_left hphase (by positivity)
    _ = |t| *((1+|(n:ℝ)|)*‖sourceAngularBetaCorrection (by simp) (by norm_num) n s
        (sobolevSourceInclusion b.val)‖) := by ring
    _ ≤ |t| *K := mul_le_mul_of_nonneg_left (hβ b hb.1 n) (abs_nonneg t)

/-- The actual beta and phase corrections are in every lq, q>1, for all real H1 inputs. -/
theorem memlp_H1_beta_phase {q : ℝ≥0∞} (hq : 1 < q)
    (a : realTypeSobolevSourceLocus) (t : ℝ) :
    Memℓp (fun n => sourceAngularBetaCorrection (by simp) (by norm_num) n s (sobolevSourceInclusion a.val)) q ∧
    Memℓp (fun n => exp ((t:ℂ)*I*sourceAngularBetaCorrection (by simp) (by norm_num) n s
      (sobolevSourceInclusion a.val))-1) q := by
  obtain ⟨U,_,ha,_,K,_,h⟩ := D.exists_local_uniform_H1_beta_phase_decay a
  exact ⟨memlp_of_inverse_bracket_bound hq _ K (fun n => (h a ha n).1),
    memlp_of_inverse_bracket_bound hq _ (|t| *K) (fun n => (h a ha n).2 t)⟩

/-- The actual beta phase error gains one sequence derivative, uniformly near each real H1 source. -/
theorem exists_local_uniform_H1_beta_phase_multipliers (a : realTypeSobolevSourceLocus) :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧ a.val ∈ U ∧
      (∀ b ∈ U, sobolevSourceInclusion b ∈ W) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ b : realTypeSobolevSourceLocus, b.val ∈ U →
        ∀ (p : ℝ≥0∞) (_ : Fact (1 ≤ p)) (r t : ℝ),
          ∃ T : WeightedCoeff (Weight.sobolev r) p →L[ℂ] WeightedCoeff (Weight.sobolev (r + 1)) p,
            (∀ c n, (T c).val n =
              (exp ((t : ℂ) * I * sourceAngularBetaCorrection (by simp) (by norm_num) n s
                (sobolevSourceInclusion b.val)) - 1) * c.val n) ∧ ‖T‖ ≤ |t| * K := by
  obtain ⟨U, hU, ha, hUW, K, hK, h⟩ := D.exists_local_uniform_H1_beta_phase_decay a
  refine ⟨U, hU, ha, hUW, K, hK, ?_⟩
  intro b hb p hp r t
  exact WeightedCoeff.exists_sobolev_gain_multiplier r _ (|t| * K) (by positivity)
    (fun n => (h b hb n).2 t)

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
