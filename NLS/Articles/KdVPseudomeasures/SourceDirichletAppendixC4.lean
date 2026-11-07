import NLS.Articles.KdVPseudomeasures.SourceDirichletFractionalPower
import NLS.ComplexAnalysis.LocalPowerToLogLinearBound
import NLS.KdV.SingularDirichletRieszLinf

/-! # The full quantitative Dirichlet estimate of Appendix C.4(ii)

The estimate holds for all original complex H^t potentials in the printed
range. A single neighborhood and cutoff work before every nearby potential
and every subsequent original index. Physical period one is retained.
-/
noncomputable section
open Set Metric Complex NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat

theorem sourceDirichletProjection_appendixC4 (r : ℝ) (hr : 1/2 < r) (hr1 : r < 1) :
    ∃ Ct : ℝ, 0 < Ct ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) 2,
      ∀ Nmin : ℕ, ∃ N : ℕ, ∃ U : Set (FourierLebesgueSpace (2:ℝ) (-r) 2),
        Nmin ≤ N ∧ IsOpen U ∧ q ∈ U ∧
        ∀ b ∈ U, IsPeriodicDistribution 1 b.val.toTempered →
          ∀ n : ℕ+, N ≤ (n:ℕ) →
            ‖singularDirichletLinfRieszProjection (hillSobolevBaseInclusion r hr1.le b)
                  (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
              singularDirichletLinfRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ ≤
              Ct*(Real.log (n:ℝ))^2/(n:ℝ)^(1-r)*‖b‖ := by
  refine ⟨1,by norm_num,?_⟩
  intro q Nmin
  obtain ⟨N,U,hN,hU,hq,hbound⟩ :=
    NLS.ComplexAnalysis.exists_local_log_squared_linear_power_bound
      (sourceFractionalDirichletProjectionError r hr1.le)
      (fun n : ℕ+ => (n:ℝ)^(-(1-r)))
      (fun n => Real.rpow_nonneg (by positivity) _)
      (sourceFractionalDirichletProjectionError_zero r hr1.le)
      (exists_local_sourceFractionalDirichletProjection_power_bound r hr hr1) q Nmin
  refine ⟨N,U,hN,hU,hq,?_⟩
  intro b hb hp n hn
  have hp' : IsPeriodicDistribution 1 (hillSobolevBaseInclusion r hr1.le b).val.toTempered := by
    rw [hillSobolevBaseInclusion_val]
    exact hp
  have he : periodOneOriginal (sourceFractionalNative r hr1.le b) =
      hillSobolevBaseInclusion r hr1.le b :=
    periodOneOriginal_extract _ hp'
  have hh := hbound n hn b hb
  unfold sourceFractionalDirichletProjectionError at hh
  rw [he] at hh
  apply (norm_singularDirichletLinfRieszProjection_sub_le_uniform _ _ _ _).trans
  apply hh.trans_eq
  rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ n)]
  ring

end NLS.Articles.KdVPseudomeasures
