import NLS.ZakharovShabat.SourcePhaseFourierSobolevBall
import NLS.ZakharovShabat.SourceBoundaryCriticalPhaseSobolevBall
import NLS.SequenceSpaces.SobolevPhaseFourierRecovery
import NLS.SequenceSpaces.WeightedTailRestriction
import NLS.SequenceSpaces.Reflection

/-! # Uniform Dirichlet-to-critical Fourier tails

The actual root Fourier remainder has a common one-order smoother tail bound on each entire real Sobolev ball.
-/

noncomputable section
open Set Metric Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- One bound and one tail cutoff suffice for the Dirichlet-to-critical
Fourier remainder on each entire real original Hs ball. -/
theorem exists_uniform_real_source_dirichlet_critical_smooth_fourier_tail_bound
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab : realTypeHigherSobolevSourceLocus s, ‖ab.val‖ ≤ R →
      ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.val.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.val.2.val j = periodOneCoefficient b j) →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K ≤ n.natAbs then
          sourceBoundaryCriticalRootDifference s .dirichlet ab.val n-(ab.val.1.val (-n)+ab.val.2.val n)/2
          else 0) ∧ ‖f‖ ≤ C := by
  obtain ⟨KU,hKU,A,hA,hu⟩ :=
    exists_uniform_real_source_boundary_phase_fourier_tail_bound s hs R hR
  obtain ⟨KV,_,B,hB,hv⟩ :=
    exists_uniform_real_source_critical_phase_fourier_tail_bound s hs R hR
  obtain ⟨KW,_,D,hD,hw⟩ :=
    exists_uniform_real_source_boundary_critical_phase_difference_bounds s hs R hR
  let K := max KU (max KV KW)
  refine ⟨K,hKU.trans_le (le_max_left _ _),(2*D)*(A+B+R)+A+B,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb
  obtain ⟨e,he,hen⟩ := hu K (le_max_left _ _) ab hab .dirichlet a b ha hb hpa hpb hca hcb
  obtain ⟨k,hk,hkn⟩ := hv K ((le_max_left _ _).trans (le_max_right _ _)) ab hab a b ha hb hpa hpb hca hcb
  let L : ScalarSobolev s := (1/2:ℂ) • (WeightedCoeff.reflection (s:ℝ) ab.val.1+ab.val.2)
  have hL (n : ℤ) : L.val n = (ab.val.1.val (-n)+ab.val.2.val n)/2 := by
    simp only [L,WeightedCoeff.smul_val,WeightedCoeff.add_val,WeightedCoeff.reflection_apply]
    ring
  have hLn : ‖L‖ ≤ R := by
    have h := norm_add_le (WeightedCoeff.reflection (s:ℝ) ab.val.1) ab.val.2
    rw [(WeightedCoeff.reflection (s:ℝ)).norm_map] at h
    have h' : ‖L‖ = (1/2:ℝ)*‖WeightedCoeff.reflection (s:ℝ) ab.val.1+ab.val.2‖ := by
      simp only [L,norm_smul,norm_div,norm_one,norm_ofNat]
    rw [h']
    linarith [norm_fst_le ab.val,norm_snd_le ab.val]
  obtain ⟨l,hl,hln⟩ := WeightedCoeff.exists_tail_restriction _ L K
  let e' : WeightedCoeff (Weight.sobolev ((s:ℝ)+1)) 2 :=
    WeightedCoeff.sobolevInclusion (by norm_num : (s:ℝ)+1 ≤ ((s+1:ℕ):ℝ)) e
  let k' : WeightedCoeff (Weight.sobolev ((s:ℝ)+1)) 2 :=
    WeightedCoeff.sobolevInclusion (by norm_num : (s:ℝ)+1 ≤ ((s+1:ℕ):ℝ)) k
  let u (n : ℤ) := if K ≤ n.natAbs then sourceBoundaryCriticalPhaseDifference s .dirichlet ab.val n else 0
  let d (n : ℤ) := if K ≤ n.natAbs then sourceBoundaryCriticalRootDifference s .dirichlet ab.val n else 0
  have hu' (n : ℤ) : u n = e'.val n-k'.val n-I*l.val n := by
    simp only [e',k',WeightedCoeff.sobolevInclusion_apply,he,hk,hl,hL]
    by_cases hn : K ≤ n.natAbs
    · simp only [u,if_pos hn,BoundaryCondition.extensionSign,
        sourceBoundaryCriticalPhaseDifference]
      ring
    · simp [u,hn]
  have hh (n : ℤ) (hn : K ≤ n.natAbs) :=
    hw ab hab .dirichlet a b ha hb hpa hpb hca hcb n
      (((le_max_right KV KW).trans (le_max_right KU _)).trans hn)
  obtain ⟨f,hf,hfn⟩ := WeightedCoeff.exists_sobolev_phase_fourier_remainder (s:ℝ) l e' k' u d D hD hu'
    (by intro n; by_cases hn : K ≤ n.natAbs
        · simpa only [u,d,if_pos hn] using (hh n hn).1
        · simp [u,d,hn])
    (by intro n; by_cases hn : K ≤ n.natAbs
        · simpa only [u,d,if_pos hn] using (hh n hn).2
        · simp [u,d,hn])
  let f' : ScalarSobolev (s+1) :=
    WeightedCoeff.sobolevInclusion (by norm_num : ((s+1:ℕ):ℝ) ≤ (s:ℝ)+1) f
  refine ⟨f',?_,?_⟩
  · intro n
    simp only [f',WeightedCoeff.sobolevInclusion_apply,hf,hl,hL]
    by_cases hn : K ≤ n.natAbs
    · simp only [d,if_pos hn]
    · simp [d,hn]
  · have he'n : ‖e'‖ ≤ A := (WeightedCoeff.norm_sobolevInclusion_le _ e).trans hen
    have hk'n : ‖k'‖ ≤ B := (WeightedCoeff.norm_sobolevInclusion_le _ k).trans hkn
    have hl'n : ‖l‖ ≤ R := hln.trans hLn
    apply (WeightedCoeff.norm_sobolevInclusion_le _ f).trans (hfn.trans ?_)
    gcongr

end NLS.ZakharovShabat
