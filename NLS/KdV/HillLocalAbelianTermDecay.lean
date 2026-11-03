import NLS.KdV.HillLocalAbelianDifferentialDecay
import NLS.KdV.HillAbelianTerminalBounds
import NLS.SequenceSpaces.ReciprocalSquareTail

/-! # Locally uniform summable bounds for the original Abelian corrections -/
noncomputable section
open Set Complex Filter Topology
open NLS.ZakharovShabat
namespace NLS.KdV

theorem exists_local_hillDirichletRegularAbelianTerm_sq_decay
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q, ∀ k : ℕ, N ≤ k →
        ‖hillDirichletRegularAbelianTerm p n hn (k+1) (by omega)‖ ≤ C/((k : ℝ)+1)^2 := by
  obtain ⟨N,hN,L,hL,hbound⟩ := exists_local_hillAbelianCosineDifferential_sq_decay q n hn
  refine ⟨max N (n+1),by omega,2*Real.pi*L,by positivity,?_⟩
  filter_upwards [hbound] with p hp
  intro k hk
  have hkN : N ≤ k+1 := by omega
  have hb := norm_regularTerm_le_of_differential_bound p n hn (k+1) (by omega) (by omega)
    (L/((k+1 : ℕ) : ℝ)^2) (by positivity) (fun θ _ => hp (k+1) hkN θ)
  convert hb using 1
  push_cast
  ring

theorem summable_hillDirichletRegularAbelianTerm
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun k : ℕ => hillDirichletRegularAbelianTerm q n hn (k+1) (by omega)) := by
  obtain ⟨N,hN,C,hC,hbound⟩ := exists_local_hillDirichletRegularAbelianTerm_sq_decay q n hn
  have hs := (NLS.ReciprocalSeries.summable_nat_reciprocal_sq_tail 1 (by omega)).mul_left C
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop N] with k hk
  simpa only [Nat.cast_one,one_div,div_eq_mul_inv,one_mul] using hbound.self_of_nhds k hk

end NLS.KdV
