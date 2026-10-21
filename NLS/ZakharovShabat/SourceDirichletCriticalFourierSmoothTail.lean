import NLS.ZakharovShabat.SourceBoundaryCriticalPhaseComparison
import NLS.SequenceSpaces.SobolevPhaseFourierRecovery
import NLS.SequenceSpaces.WeightedTailRestriction
import NLS.SequenceSpaces.Reflection

/-! # The Dirichlet-to-critical Fourier tail

The actual root difference has its original Fourier half-sum with a uniform H^(s+1) tail for matching smooth periodic representatives.
-/

noncomputable section
open Set Metric Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The Dirichlet-to-critical difference has its original Fourier half-sum
with a uniformly bounded one-order smoother tail on the original Hs source.
At this stage the matching smooth periodic representatives remain explicit. -/
theorem exists_local_source_dirichlet_critical_smooth_fourier_tail_bound
    (s : ℕ) (hs : 1 ≤ s) (a₀ : realTypeHigherSobolevSourceLocus s) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a₀.val ∈ U ∧
      ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ ab ∈ U,
      ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K ≤ n.natAbs then
          sourceBoundaryCriticalRootDifference s .dirichlet ab n-(ab.1.val (-n)+ab.2.val n)/2
          else 0) ∧ ‖f‖ ≤ C := by
  obtain ⟨U,hU,haU,KU,hKU,A,hA,hu⟩ :=
    exists_local_source_boundary_phase_smooth_fourier_tail_bound s hs a₀ .dirichlet
  obtain ⟨V,hV,haV,KV,_,B,hB,hv⟩ :=
    exists_local_source_critical_phase_smooth_tail_bound s hs a₀
  obtain ⟨W,hW,haW,KW,_,D,hD,hw⟩ :=
    exists_local_source_boundary_critical_phase_difference_bounds s hs a₀ .dirichlet
  let K := max KU (max KV KW)
  let R := ‖a₀.val‖+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨((U ∩ V) ∩ W) ∩ ball a₀.val 1,((hU.inter hV).inter hW).inter isOpen_ball,
    ⟨⟨⟨haU,haV⟩,haW⟩,mem_ball_self (by norm_num)⟩,K,hKU.trans_le (le_max_left _ _),
    (2*D)*(A+B+R)+A+B,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb
  have habR : ‖ab‖ ≤ R := by
    have h : ‖ab-a₀.val‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hab.2
    have h' := norm_add_le (ab-a₀.val) a₀.val
    simp only [sub_add_cancel] at h'
    dsimp only [R]
    linarith
  obtain ⟨e₀,he₀,hen₀⟩ := (hu ab hab.1.1.1).2 a b ha hb hpa hpb hca hcb
  obtain ⟨k₀,hk₀,hkn₀⟩ := (hv ab hab.1.1.2).2 a b ha hb hpa hpb hca hcb
  obtain ⟨e,he,hen⟩ := WeightedCoeff.exists_tail_restriction_of_coordinates _ e₀ _ KU K
    (le_max_left _ _) he₀
  obtain ⟨k,hk,hkn⟩ := WeightedCoeff.exists_tail_restriction_of_coordinates _ k₀ _ KV K
    ((le_max_left _ _).trans (le_max_right _ _)) hk₀
  let L : ScalarSobolev s := (1/2:ℂ) • (WeightedCoeff.reflection (s:ℝ) ab.1+ab.2)
  have hL (n : ℤ) : L.val n = (ab.1.val (-n)+ab.2.val n)/2 := by
    simp only [L,WeightedCoeff.smul_val,WeightedCoeff.add_val,WeightedCoeff.reflection_apply]
    ring
  have hLn : ‖L‖ ≤ R := by
    have h := norm_add_le (WeightedCoeff.reflection (s:ℝ) ab.1) ab.2
    rw [(WeightedCoeff.reflection (s:ℝ)).norm_map] at h
    have h' : ‖L‖ = (1/2:ℝ)*‖WeightedCoeff.reflection (s:ℝ) ab.1+ab.2‖ := by
      simp only [L,norm_smul,norm_div,norm_one,norm_ofNat]
    rw [h']
    linarith [norm_fst_le ab,norm_snd_le ab]
  obtain ⟨l,hl,hln⟩ := WeightedCoeff.exists_tail_restriction _ L K
  let e' : WeightedCoeff (Weight.sobolev ((s:ℝ)+1)) 2 :=
    WeightedCoeff.sobolevInclusion (by norm_num : (s:ℝ)+1 ≤ ((s+1:ℕ):ℝ)) e
  let k' : WeightedCoeff (Weight.sobolev ((s:ℝ)+1)) 2 :=
    WeightedCoeff.sobolevInclusion (by norm_num : (s:ℝ)+1 ≤ ((s+1:ℕ):ℝ)) k
  let u (n : ℤ) := if K ≤ n.natAbs then sourceBoundaryCriticalPhaseDifference s .dirichlet ab n else 0
  let d (n : ℤ) := if K ≤ n.natAbs then sourceBoundaryCriticalRootDifference s .dirichlet ab n else 0
  have hu' (n : ℤ) : u n = e'.val n-k'.val n-I*l.val n := by
    simp only [e',k',WeightedCoeff.sobolevInclusion_apply,he,hk,hl,hL]
    by_cases hn : K ≤ n.natAbs
    · simp only [u,if_pos hn,BoundaryCondition.extensionSign,
        sourceBoundaryCriticalPhaseDifference]
      ring
    · simp [u,hn]
  have hh (n : ℤ) (hn : K ≤ n.natAbs) :=
    hw ab hab.1.2 a b ha hb hpa hpb hca hcb n
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
  · have he'n : ‖e'‖ ≤ A := (WeightedCoeff.norm_sobolevInclusion_le _ e).trans (hen.trans hen₀)
    have hk'n : ‖k'‖ ≤ B := (WeightedCoeff.norm_sobolevInclusion_le _ k).trans (hkn.trans hkn₀)
    have hl'n : ‖l‖ ≤ R := hln.trans hLn
    apply (WeightedCoeff.norm_sobolevInclusion_le _ f).trans (hfn.trans ?_)
    gcongr

end NLS.ZakharovShabat
