import NLS.ZakharovShabat.SourceStandardRootPairedProductUniform
import NLS.ZakharovShabat.SourceStandardRootContourLocalStability
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Holomorphic paired standard-root product

The noncentral periodic gap segments form a locally finite family in the
spectral plane. Their complement is open, so compact-uniform convergence
of the analytic finite paired products gives an analytic infinite product.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At a fixed source potential every periodic gap segment lies within
one common radius of its free lattice center `πk`. -/
theorem exists_sourcePeriodicSegment_uniform_freeBall
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    ∃ R : ℝ, 0 < R ∧ ∀ k : ℤ,
      sourcePeriodicSegment hp hp1 ψ k ⊆
        Metric.ball ((Real.pi : ℂ)*k) R := by
  let a := canonicalPeriodicLeftDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let b := canonicalPeriodicRightDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let R : ℝ := ‖a‖ + ‖b‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R, hR, ?_⟩
  intro k
  have ha := lp.norm_apply_le_norm
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' a k
  have hb := lp.norm_apply_le_norm
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' b k
  have hleft : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) k ∈ Metric.ball ((Real.pi : ℂ)*k) R := by
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖a k‖ < R
    dsimp [R]
    nlinarith [lp.norm_nonneg' b]
  have hright : canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) k ∈ Metric.ball ((Real.pi : ℂ)*k) R := by
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖b k‖ < R
    dsimp [R]
    nlinarith [lp.norm_nonneg' a]
  exact (convex_ball ((Real.pi : ℂ)*k) R).segment_subset hleft hright

/-- Only finitely many periodic gap segments can meet a fixed unit
neighborhood in the spectral plane. -/
theorem exists_sourcePeriodicSegment_tail_avoids_ball
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z₀ : ℂ) :
    ∃ N : ℕ, ∀ k : ℤ, N < k.natAbs →
      Metric.ball z₀ 1 ⊆ (sourcePeriodicSegment hp hp1 ψ k)ᶜ := by
  obtain ⟨R, _, hseg⟩ :=
    exists_sourcePeriodicSegment_uniform_freeBall hp hp1 ψ
  obtain ⟨N, hN⟩ := exists_nat_gt ((‖z₀‖+1+R)/Real.pi)
  refine ⟨N, ?_⟩
  intro k hk w hw hws
  have hwnear : ‖w-z₀‖ < 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hwseg : ‖w-((Real.pi : ℂ)*k)‖ < R := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hseg k hws
  have hwbound : ‖w‖ ≤ ‖w-z₀‖ + ‖z₀‖ := by
    have he : w = (w-z₀)+z₀ := by ring
    calc
      ‖w‖ = ‖(w-z₀)+z₀‖ := congrArg norm he
      _ ≤ ‖w-z₀‖ + ‖z₀‖ := norm_add_le _ _
  have hcenterbound : ‖(Real.pi : ℂ)*k‖ ≤
      ‖w-((Real.pi : ℂ)*k)‖ + ‖w‖ := by
    have he : (Real.pi : ℂ)*k = ((Real.pi : ℂ)*k-w)+w := by ring
    calc
      ‖(Real.pi : ℂ)*k‖ = ‖((Real.pi : ℂ)*k-w)+w‖ := congrArg norm he
      _ ≤ ‖((Real.pi : ℂ)*k)-w‖ + ‖w‖ := norm_add_le _ _
      _ = ‖w-((Real.pi : ℂ)*k)‖ + ‖w‖ := by rw [norm_sub_rev]
  have habs : |(k : ℝ)| = (k.natAbs : ℝ) := by
    simp only [Nat.cast_natAbs, Int.cast_abs]
  have hkr : (N : ℝ) < |(k : ℝ)| := by
    rw [habs]
    exact_mod_cast hk
  have hlarge : ‖z₀‖+1+R < Real.pi*|(k : ℝ)| := by
    have ht := lt_trans hN hkr
    simpa only [mul_comm] using (div_lt_iff₀ Real.pi_pos).mp ht
  have hcenter : ‖(Real.pi : ℂ)*k‖ = Real.pi*|(k : ℝ)| := by
    simp [Complex.norm_intCast, abs_of_pos Real.pi_pos]
  rw [hcenter] at hcenterbound
  linarith

/-- The complement of all noncentral periodic gap segments is open.
Local finiteness reduces this infinite intersection to finitely many
closed segments near each spectral point. -/
theorem isOpen_sourceStandardRootPairedDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    IsOpen (sourceStandardRootPairedDomain hp hp1 ψ) := by
  apply isOpen_iff_forall_mem_open.mpr
  intro z hz
  obtain ⟨N, htail⟩ :=
    exists_sourcePeriodicSegment_tail_avoids_ball hp hp1 ψ z
  let s : Finset ℤ := (Finset.Icc (-(N : ℤ)) N).erase 0
  let U : Set ℂ := Metric.ball z 1 ∩
    ⋂ k ∈ s, (sourcePeriodicSegment hp hp1 ψ k)ᶜ
  have hUopen : IsOpen U := by
    exact isOpen_ball.inter (isOpen_biInter_finset
      (fun k _ => (isClosed_sourcePeriodicSegment hp hp1 ψ k).isOpen_compl))
  have hzU : z ∈ U := by
    refine ⟨mem_ball_self (by norm_num), ?_⟩
    simp only [Set.mem_iInter]
    intro k hks
    have hk0 : k ≠ 0 := (Finset.mem_erase.mp hks).1
    exact hz k hk0
  have hUsub : U ⊆ sourceStandardRootPairedDomain hp hp1 ψ := by
    intro w hw k hk0
    by_cases hks : k ∈ s
    · exact (Set.mem_iInter.mp (Set.mem_iInter.mp hw.2 k) hks)
    · have hnotIcc : k ∉ Finset.Icc (-(N : ℤ)) N := by
        intro hIcc
        exact hks (Finset.mem_erase.mpr ⟨hk0, hIcc⟩)
      have hklarge : N < k.natAbs := by
        simp only [Finset.mem_Icc] at hnotIcc
        omega
      exact htail k hklarge hw.1
  exact ⟨U, hUsub, hUopen, hzU⟩

/-- The paired product converges locally uniformly throughout the open
spectral complement of the noncentral periodic gaps. -/
theorem hasProdLocallyUniformlyOn_sourceStandardRootPairedFactor
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    HasProdLocallyUniformlyOn
      (fun j z => sourceStandardRootPairedFactor hp hp1 ψ z j)
      (fun z => sourceStandardRootPairedProduct hp hp1 ψ z)
      (sourceStandardRootPairedDomain hp hp1 ψ) := by
  apply hasProdLocallyUniformlyOn_of_forall_compact
    (isOpen_sourceStandardRootPairedDomain hp hp1 ψ)
  intro K hKsub hKcompact
  exact hasProdUniformlyOn_sourceStandardRootPairedFactor
    hp hp1 ψ K hKcompact hKsub

/-- The infinite omitted-zero paired standard-root product is analytic
at every spectral parameter outside the noncentral gap segments. -/
theorem sourceStandardRootPairedProduct_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    AnalyticOnNhd ℂ (sourceStandardRootPairedProduct hp hp1 ψ)
      (sourceStandardRootPairedDomain hp hp1 ψ) := by
  have hfactor (j : ℕ) :
      DifferentiableOn ℂ (fun z => sourceStandardRootPairedFactor hp hp1 ψ z j)
        (sourceStandardRootPairedDomain hp hp1 ψ) := by
    intro z hz
    exact (sourceStandardRootPairedFactor_analyticAt hp hp1 ψ z hz j).differentiableAt.differentiableWithinAt
  have hdiff : DifferentiableOn ℂ (sourceStandardRootPairedProduct hp hp1 ψ)
      (sourceStandardRootPairedDomain hp hp1 ψ) := by
    apply (hasProdLocallyUniformlyOn_sourceStandardRootPairedFactor hp hp1 ψ).differentiableOn
      (Filter.Eventually.of_forall (fun s =>
        DifferentiableOn.fun_finsetProd (fun j _ => hfactor j)))
      (isOpen_sourceStandardRootPairedDomain hp hp1 ψ)
  exact hdiff.analyticOnNhd (isOpen_sourceStandardRootPairedDomain hp hp1 ψ)

/-- Pointwise form of spectral analyticity for the infinite product. -/
theorem sourceStandardRootPairedProduct_analyticAt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceStandardRootPairedDomain hp hp1 ψ) :
    AnalyticAt ℂ (sourceStandardRootPairedProduct hp hp1 ψ) z :=
  sourceStandardRootPairedProduct_analyticOnNhd hp hp1 ψ z hz

end NLS.ZakharovShabat
