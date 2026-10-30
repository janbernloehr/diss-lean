import NLS.ZakharovShabat.SourceNormalizedActionComplexSequenceContinuity
import NLS.ZakharovShabat.SourceNormalizedActionCollapsedPositive
import NLS.ZakharovShabat.SourceStandardRootProductFactors
import NLS.SequenceSpaces.CoefficientDecay
import NLS.ZakharovShabat.SourceEquation2_19

/-!
# Locally uniform tails of normalized actions and their principal roots

For every positive error tolerance and every real source, one complex
neighborhood and one cutoff control both tails at all signed indices.
The neighborhood may depend on the tolerance. This is precisely the
quantifier order of `TendstoLocallyUniformlyOn`, and implies uniform
convergence on each compact subset of the real source locus.

Norm continuity of the sequence-valued deviation supplies the common
neighborhood; decay of the fixed base sequence supplies the cutoff.
The normalization is four times the filled action quotient, including
collapsed gaps. The principal-root error has the same bound.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One tolerance-dependent complex neighborhood and cutoff control both
tails, including at collapsed gaps and for positive and negative indices. -/
theorem exists_local_sourceNormalizedAction_and_root_tail_lt
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∃ N : ℕ,
      ∀ ψ ∈ V, ∀ n : ℤ, N ≤ n.natAbs →
        ‖4 * sourceNormalizedActionComplexExtension hp hp1 n ψ - 1‖ < ε ∧
        ‖sourceNormalizedActionRoot hp hp1 n ψ - 1‖ < ε := by
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p := by
    rw [ENNReal.ofReal_le_iff_le_toReal hp]
    linarith [ENNReal.toReal_nonneg (a := p)]
  obtain ⟨U,hU,hφU,F,hF,hcont⟩ :=
    exists_local_sourceNormalizedActionDeviation_continuousMap
      (q := p) hp hp1 hp1 hp hhalf φ hreal
  obtain ⟨N,hN⟩ := Coeff.exists_cutoff_norm_apply_lt hp (F φ) (half_pos hε)
  have hcontAt : ContinuousAt F φ :=
    (hcont φ hφU).continuousAt (hU.mem_nhds hφU)
  have hnear : ∀ᶠ ψ : CoeffPair p in 𝓝 φ, ‖F ψ - F φ‖ < ε/2 := by
    simpa only [mem_ball,dist_eq_norm] using
      hcontAt.eventually (Metric.ball_mem_nhds (F φ) (half_pos hε))
  obtain ⟨V,hVsub,hV,hφV⟩ := _root_.mem_nhds_iff.mp hnear
  refine ⟨U ∩ V,hU.inter hV,⟨hφU,hφV⟩,N,?_⟩
  intro ψ hψ n hn
  have hcoord : ‖F ψ n - F φ n‖ ≤ ‖F ψ - F φ‖ := by
    simpa using lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' (F ψ - F φ) n
  have hsmall : ‖4 * sourceNormalizedActionComplexExtension hp hp1 n ψ - 1‖ < ε := by
    change ‖sourceNormalizedActionDeviation hp hp1 ψ n‖ < ε
    rw [← hF ψ hψ.1 n]
    have htri := norm_le_norm_sub_add (F ψ n) (F φ n)
    have hbase := hN n hn
    have hclose := hcoord.trans_lt (hVsub hψ.2)
    linarith
  exact ⟨hsmall,(norm_sqrt_sub_one_le
    (4 * sourceNormalizedActionComplexExtension hp hp1 n ψ)).trans_lt hsmall⟩

/-- The factor-four normalized actions tend locally uniformly to one on
the real locus, with the filled value used at every collapsed gap. -/
theorem tendstoLocallyUniformlyOn_sourceNormalizedAction
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    TendstoLocallyUniformlyOn
      (fun n ψ => 4 * sourceNormalizedActionComplexExtension hp hp1 n ψ)
      (fun _ => (1 : ℂ)) (Filter.comap Int.natAbs atTop) (realTypeSourceLocus p) := by
  apply Metric.tendstoLocallyUniformlyOn_iff.mpr
  intro ε hε φ hφ
  obtain ⟨V,hV,hφV,N,hbound⟩ :=
    exists_local_sourceNormalizedAction_and_root_tail_lt hp hp1 φ hφ hε
  refine ⟨V,mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hφV),?_⟩
  have hlarge : ∀ᶠ n : ℤ in Filter.comap Int.natAbs atTop, N ≤ n.natAbs :=
    Filter.eventually_comap.mpr ((eventually_ge_atTop N).mono
      (fun _ hk _ hn => hn.symm ▸ hk))
  filter_upwards [hlarge] with n hn ψ hψ
  simpa only [dist_comm (1 : ℂ),dist_eq_norm] using (hbound ψ hψ n hn).1

/-- The same locally uniform limit holds for the principal roots. -/
theorem tendstoLocallyUniformlyOn_sourceNormalizedActionRoot
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    TendstoLocallyUniformlyOn
      (fun n ψ => sourceNormalizedActionRoot hp hp1 n ψ)
      (fun _ => (1 : ℂ)) (Filter.comap Int.natAbs atTop) (realTypeSourceLocus p) := by
  apply Metric.tendstoLocallyUniformlyOn_iff.mpr
  intro ε hε φ hφ
  obtain ⟨V,hV,hφV,N,hbound⟩ :=
    exists_local_sourceNormalizedAction_and_root_tail_lt hp hp1 φ hφ hε
  refine ⟨V,mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hφV),?_⟩
  have hlarge : ∀ᶠ n : ℤ in Filter.comap Int.natAbs atTop, N ≤ n.natAbs :=
    Filter.eventually_comap.mpr ((eventually_ge_atTop N).mono
      (fun _ hk _ hn => hn.symm ▸ hk))
  filter_upwards [hlarge] with n hn ψ hψ
  simpa only [dist_comm (1 : ℂ),dist_eq_norm] using (hbound ψ hψ n hn).2

/-- On each compact real source set, both tails converge uniformly. -/
theorem tendstoUniformlyOn_sourceNormalizedAction_and_root_of_isCompact
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    {K : Set (CoeffPair p)} (hK : IsCompact K) (hreal : K ⊆ realTypeSourceLocus p) :
    TendstoUniformlyOn
      (fun n ψ => 4 * sourceNormalizedActionComplexExtension hp hp1 n ψ)
      (fun _ => (1 : ℂ)) (Filter.comap Int.natAbs atTop) K ∧
    TendstoUniformlyOn
      (fun n ψ => sourceNormalizedActionRoot hp hp1 n ψ)
      (fun _ => (1 : ℂ)) (Filter.comap Int.natAbs atTop) K :=
  ⟨(tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
      ((tendstoLocallyUniformlyOn_sourceNormalizedAction hp hp1).mono hreal),
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
      ((tendstoLocallyUniformlyOn_sourceNormalizedActionRoot hp hp1).mono hreal)⟩

/-- The final real-locus assertion in Section 11 for the actual filled
indexed quotient: strict positivity and the locally uniform limit one. -/
theorem SourceEquation2_19Data.normalized_real_positive_and_tail
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    (H : SourceEquation2_19Data hp hp1 W₀) (Hn : SourceTheorem11_2Data hp hp1 W₀ W)
    (hreal : realTypeSourceLocus p ⊆ W) :
    (∀ ψ ∈ realTypeSourceLocus p, ∀ n : ℤ,
      0 < (4 * sourceNormalizedIndexedAction hp hp1 n ψ).re) ∧
    TendstoLocallyUniformlyOn
      (fun n ψ => 4 * sourceNormalizedIndexedAction hp hp1 n ψ)
      (fun _ => (1 : ℂ)) (Filter.comap Int.natAbs atTop) (realTypeSourceLocus p) := by
  constructor
  · intro ψ hψ n
    rw [H.normalized_eq_theorem11_2 Hn ψ (hreal hψ) n]
    simpa [Complex.mul_re] using
      mul_pos (by norm_num : (0 : ℝ) < 4) (Hn.re_pos ψ (hreal hψ) n)
  · apply (tendstoLocallyUniformlyOn_sourceNormalizedAction hp hp1).congr
    intro n ψ hψ
    dsimp only
    rw [H.normalized_eq_theorem11_2 Hn ψ (hreal hψ) n]

end NLS.ZakharovShabat
