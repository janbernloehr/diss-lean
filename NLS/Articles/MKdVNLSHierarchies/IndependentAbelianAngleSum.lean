import NLS.MKdV.MiuraFullPhaseGenerator

/-! # Final independent canonical phase and the full angle-sum clause

The independent mKdV phase is the spectral conjugate of the original full
Hill Abelian phase. Its complete physical action rotation and the final
angle sum hold on the full original real H¹ domain, including arbitrary
support and every closed action other than the selected angle's own one.
The angle sum is represented by its full unit phase, modulo exactly 2π.
-/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.MKdV NLS.ZakharovShabat
namespace NLS.Articles.MKdVNLSHierarchies

theorem independent_full_phase_complete_action_rotation
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (n : ℕ) (hn : 1 ≤ n)
    (j : ℕ) (hj : 1 ≤ j) (t : ℝ) :
    miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j t) =
      Complex.exp (-(if n = j then I else 0)*(t:ℂ))*miuraNativeOppositeAbelianPhase s hs n hn a :=
  miuraNativeOppositeAbelianPhase_actionFlow s hs a n hn j hj t

theorem independent_full_phase_actual_action_generator
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (n : ℕ) (hn : 1 ≤ n)
    (j : ℕ) (hj : 1 ≤ j) (t : ℝ) :
    HasDerivAt (fun r => miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j r))
      (-(if n = j then I else 0)*miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j t)) t :=
  hasDerivAt_miuraNativeOppositeAbelianPhase_actionFlow s hs a n hn j hj t

/-- The final source clause, on every native Hˢ class, s≥1. The factor
uses the entire original physical action sequence and literal signed mean.
No additional analyticity of this angle-sum factor is asserted. -/
theorem theorem4_iii_independent_phase_sum (s : ℕ) (hs : 1 ≤ s) (n : ℕ) (hn : 1 ≤ n) :
    ∃ f : MiuraNativeActionMeanTarget s → ℂ,∀ a : MiuraRealSobolevSource s,
      f (miuraNativeActionMeanMap s a.val) =
        miuraNativeNLSUnitPhase s n a*miuraNativeOppositeAbelianPhase s hs n hn a :=
  exists_miuraIndependentAbelianPhase_action_factor s hs n hn

/-- Original real H¹ domain of Theorem4(iii), retaining the full unit
phases rather than their squares. The product is unit norm on precisely
the selected original open-action locus. -/
theorem theorem4_iii_independent_angle_sum (n : ℕ) (hn : 1 ≤ n) :
    ∃ f : MiuraNativeActionMeanTarget 1 → ℂ,∀ a : MiuraRealSobolevSource 1,
      f (miuraNativeActionMeanMap 1 a.val) =
        miuraNativeNLSUnitPhase 1 n a*miuraNativeOppositeAbelianPhase 1 (by norm_num) n hn a ∧
      (miuraNativeNLSAngularCoordinate 1 n a ≠ 0 → ‖f (miuraNativeActionMeanMap 1 a.val)‖ = 1) := by
  obtain ⟨f,hf⟩ := theorem4_iii_independent_phase_sum 1 (by norm_num) n hn
  refine ⟨f,fun a => ⟨hf a,fun ha => ?_⟩⟩
  rw [hf a,norm_mul,norm_miuraNativeNLSUnitPhase 1 n a ha,
    norm_miuraNativeOppositeAbelianPhase 1 (by norm_num) n hn a ha,one_mul]

/-- For any real representatives of the two actual phases, the exponential
of their sum is the same function of all actions and signed mean. -/
theorem theorem4_iii_angle_sum_representatives (n : ℕ) (hn : 1 ≤ n) :
    ∃ f : MiuraNativeActionMeanTarget 1 → ℂ,∀ (a : MiuraRealSobolevSource 1) (θ ϑ : ℝ),
      Complex.exp (I*(θ:ℂ)) = miuraNativeNLSUnitPhase 1 n a →
      Complex.exp (I*(ϑ:ℂ)) = miuraNativeOppositeAbelianPhase 1 (by norm_num) n hn a →
      Complex.exp (I*((θ+ϑ:ℝ):ℂ)) = f (miuraNativeActionMeanMap 1 a.val) := by
  obtain ⟨f,hf⟩ := theorem4_iii_independent_phase_sum 1 (by norm_num) n hn
  refine ⟨f,fun a θ ϑ hθ hϑ => ?_⟩
  rw [Complex.ofReal_add,mul_add,Complex.exp_add,hθ,hϑ]
  exact (hf a).symm

end NLS.Articles.MKdVNLSHierarchies
