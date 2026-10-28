import NLS.ZakharovShabat.ResonantProofRoots
import NLS.ZakharovShabat.SourceLemma6_9
import NLS.ZakharovShabat.SourcePeriodTwoCanonicalMidpointGap

/-! # The root proof of Lemma 6.9 for original period-two input

Counts, the simple diagonal zero, full-strip localization and branch-free
estimates share one original neighborhood. The counted determinant pair
agrees with the canonical periodic pair, including repeated roots.
-/
noncomputable section
open NLS.ComplexAnalysis
namespace NLS.ZakharovShabat
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source coefficients satisfy both literal Rouche comparisons and all three counts. -/
theorem SourceResonantStripControl.two_step_rouche {hp : p ≠ ⊤} {φ : CoeffPair p} {n : ℤ}
    (hc : SourceResonantStripControl hp φ n) :
    let h := fun z => z-(Real.pi : ℂ)*n-sourceResonantAFunction hp φ n z
    analyticZeroCount h (refinedResonantDisk n) = 1 ∧
    analyticZeroCount (fun z => (h z)^2) (refinedResonantDisk n) = 2 ∧
    analyticZeroCount (sourceResonantDeterminantFunction hp φ n) (refinedResonantDisk n) = 2 ∧
    ∀ z ∈ resonantStrip n, z ∉ refinedResonantDisk n →
      sourceResonantDeterminantFunction hp φ n z ≠ 0 := by
  have ha (i j : Fin 2) : AnalyticOnNhd ℂ
      (fun z => sourceCorrectionEntryFunction hp φ n z i j) (resonantStrip n) := by
    intro z hz
    exact (analyticAt_sourceCorrectionEntryFunction hp φ n z hz
      ((hc.small z hz).trans_lt (by norm_num)) i j).comp
      (analyticAt_const.prod analyticAt_id)
  exact resonantProof_two_step_rouche n _ _ _ (ha 0 0) (ha 1 0) (ha 0 1)
    hc.diagonal hc.positive hc.negative

/-- The root-counting and branch-free estimates in the proof of Lemma 6.9, for the original source functions. -/
structure SourceLemma69Proof (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) : Prop where
  diagonal_count : analyticZeroCount
    (fun z => z-(Real.pi : ℂ)*n-sourceResonantAFunction hp φ n z) (refinedResonantDisk n) = 1
  diagonal_square_count : analyticZeroCount
    (fun z => (z-(Real.pi : ℂ)*n-sourceResonantAFunction hp φ n z)^2) (refinedResonantDisk n) = 2
  determinant_disk_count : analyticZeroCount (sourceResonantDeterminantFunction hp φ n)
    (refinedResonantDisk n) = 2
  determinant_strip_count : analyticZeroCount (sourceResonantDeterminantFunction hp φ n)
    (resonantStrip n) = 2
  no_exterior_roots : ∀ z ∈ resonantStrip n, z ∉ refinedResonantDisk n →
    sourceResonantDeterminantFunction hp φ n z ≠ 0
  diagonal_simple : ∃ x ∈ refinedResonantDisk n,
    x-(Real.pi : ℂ)*n-sourceResonantAFunction hp φ n x = 0 ∧
    analyticOrderAt (fun z => z-(Real.pi : ℂ)*n-sourceResonantAFunction hp φ n z) x = 1 ∧
    ∀ z ∈ resonantStrip n, z-(Real.pi : ℂ)*n-sourceResonantAFunction hp φ n z = 0 ↔ z = x
  derivative_bound : ∀ z ∈ refinedResonantDisk n, ‖deriv (sourceResonantAFunction hp φ n) z‖ ≤ 1/8
  residual_norm : ∀ z : ℂ, sourceResonantDeterminantFunction hp φ n z = 0 →
    ‖z-(Real.pi : ℂ)*n-sourceResonantAFunction hp φ n z‖ =
      Real.sqrt ‖sourceResonantBPlusFunction hp φ n z*sourceResonantBMinusFunction hp φ n z‖
  gap_bound : ∀ x ∈ resonantStrip n, ∀ y ∈ resonantStrip n,
    sourceResonantDeterminantFunction hp φ n x = 0 →
    sourceResonantDeterminantFunction hp φ n y = 0 → ‖x-y‖^2 ≤ 6*sourceResonantBProductSup hp φ n

/-- Actual strip control supplies every root-proof assertion, including the unique simple diagonal zero. -/
theorem SourceResonantStripControl.proof_roots {hp : p ≠ ⊤} {φ : CoeffPair p} {n : ℤ}
    (hc : SourceResonantStripControl hp φ n) : SourceLemma69Proof hp φ n := by
  have ha : AnalyticOnNhd ℂ (sourceResonantAFunction hp φ n) (resonantStrip n) := by
    intro z hz
    exact (analyticAt_sourceCorrectionEntryFunction hp φ n z hz
      ((hc.small z hz).trans_lt (by norm_num)) 0 0).comp
      (analyticAt_const.prod analyticAt_id)
  obtain ⟨hcount,hsquare,hdet,hext⟩ := SourceResonantStripControl.two_step_rouche hc
  refine ⟨hcount,hsquare,hdet,?_,hext,resonantProof_unique_simple_diagonal n _ ha hc.diagonal,
    hc.deriv_bound,?_,?_⟩
  · rw [analyticZeroCount_congr_set (sourceResonantDeterminantFunction hp φ n)
      (K := resonantStrip n) (L := refinedResonantDisk n) ?_,hdet]
    intro z hz0
    exact ⟨fun hz => by_contra (fun hout => hext z hz hout hz0),
      fun hz => refinedResonantDisk_subset_strip n hz⟩
  · intro z hz0
    exact (resonantProof_root_modulus (z-(Real.pi : ℂ)*n) _ _ _ hz0).1
  · intro x hx y hy hx0 hy0
    simpa only [sourceResonantBProductSup_unit] using
      resonantDeterminant_root_gap_le hp SpectralWeight.one (unitWeightedPairEquiv φ) n
        ha (fun z hz => ⟨hc.diagonal z hz,hc.negative z hz,hc.positive z hz⟩)
        x y hx hy hx0 hy0

/-- One original open convex neighborhood and threshold support the complete root-proof assertions. -/
theorem sourceLemma6_9_proof_roots (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → SourceLemma69Proof hp ψ n := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hd⟩ := exists_uniform_sourceResonantDeterminant_control hp hp1 φ
  exact ⟨N,hN,U,ho,hc,hφ,h0,fun ψ hψ n hn => SourceResonantStripControl.proof_roots ((hd n hn).2 ψ hψ)⟩

/-- Original determinant roots retain their actual periodic spectral multiplicities. -/
theorem SourceResonantRootPair.toEndpoints {hp : p ≠ ⊤} {φ : CoeffPair p} {n : ℤ} {x y : ℂ}
    (h : SourceResonantRootPair hp φ n x y) :
    PeriodicEndpointPair hp (CoeffPair.toMax p φ) n x y := by
  refine ⟨h.left_mem,h.right_mem,?_,h.multiplicity_eq_count⟩
  intro z hz
  simpa only [weightedBaseToPair_unitWeightedPairEquiv] using
    (sourcePeriodTwoSpectrum_iff hp φ z).symm.trans (h.spectrum_iff z hz)

/-- One common neighborhood identifies the original determinant roots with the canonical period-two pair, including multiplicities and gap norms. -/
theorem sourceLemma6_9_proof_canonical (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∃ ξ η : ℤ → ℂ, ∀ n : ℤ, N ≤ n.natAbs →
        SourceLemma69Proof hp ψ n ∧ SourceResonantRootPair hp ψ n (ξ n) (η n) ∧
        ({ξ n,η n} : Multiset ℂ) =
          {sourcePeriodTwoCanonicalLeft hp hp1 ψ n,sourcePeriodTwoCanonicalRight hp hp1 ψ n} ∧
        ‖sourcePeriodTwoCanonicalGap hp hp1 ψ n‖ = ‖ξ n-η n‖ := by
  obtain ⟨N₁,hN₁,V,hoV,hcV,hφV,h0V,hcontrol,hroots⟩ := sourceLemma6_9 hp hp1 φ
  obtain ⟨N₂,_,W,hoW,hcW,hφW,h0W,hcanon⟩ :=
    sourceProposition6_1_canonical_asymptotics hp hp1 φ (by norm_num : (0 : ℝ) < 1)
  refine ⟨max N₁ (N₂+1),by omega,V ∩ W,hoV.inter hoW,hcV.inter hcW,
    ⟨hφV,hφW⟩,⟨h0V,h0W⟩,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hr,_⟩ := hroots ψ hψ.1
  refine ⟨ξ,η,?_⟩
  intro n hn
  have hpair := hr n (by omega)
  have he := (SourceResonantRootPair.toEndpoints hpair).multiset_eq ((hcanon ψ hψ.2).1.distant n (by omega))
  refine ⟨SourceResonantStripControl.proof_roots ((hcontrol n (by omega)).2 ψ hψ.1),hpair,he,?_⟩
  have hperm : List.Perm [ξ n,η n]
      [sourcePeriodTwoCanonicalLeft hp hp1 ψ n,sourcePeriodTwoCanonicalRight hp hp1 ψ n] :=
    Multiset.coe_eq_coe.mp he
  have heq : (ξ n = sourcePeriodTwoCanonicalLeft hp hp1 ψ n ∧
      η n = sourcePeriodTwoCanonicalRight hp hp1 ψ n) ∨
      (ξ n = sourcePeriodTwoCanonicalRight hp hp1 ψ n ∧
      η n = sourcePeriodTwoCanonicalLeft hp hp1 ψ n) := by
    simpa only [List.cons.injEq,and_true] using List.perm_pair.mp hperm
  rcases heq with ⟨hx,hy⟩ | ⟨hx,hy⟩ <;>
    simp only [sourcePeriodTwoCanonicalGap,hx,hy,norm_sub_rev]

end NLS.ZakharovShabat
