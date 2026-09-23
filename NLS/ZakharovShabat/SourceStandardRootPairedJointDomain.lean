import NLS.ZakharovShabat.SourceStandardRootPairedProductHolomorphic
import NLS.ZakharovShabat.SourceStandardRootPairedProductJointUniform
import NLS.ZakharovShabat.CanonicalPeriodicDisplacementBounds
import NLS.ZakharovShabat.SourceSymmetricContour
import NLS.ComplexAnalysis.SymmetricSegmentIncidence

/-!
# Source-uniform separation of distant periodic gaps

The canonical periodic endpoint displacements have a common norm bound
on a source neighborhood. Consequently every gap segment there stays
within one radius of its free lattice center, and all sufficiently
distant gaps avoid a fixed bounded spectral neighborhood. This is the
tail part of the joint analytic domain for the standard-root product.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Near any source potential, every indexed periodic gap lies within
one common radius of its free lattice center. -/
theorem exists_uniform_sourcePeriodicSegment_freeBall
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ R : ℝ, 0 < R ∧ ∀ ψ ∈ V, ∀ k : ℤ,
        sourcePeriodicSegment hp hp1 ψ k ⊆
          Metric.ball ((Real.pi : ℂ)*k) R := by
  obtain ⟨_, _, U, hUopen, _, hφU, _, B, hB, hdata⟩ :=
    exists_uniform_small_canonicalPeriodicDisplacements hp hp1
      (periodOnePotential φ) (by norm_num : (0 : ℝ) < 1)
  let V : Set (CoeffPair p) := periodOnePotential ⁻¹' U
  have hVopen : IsOpen V :=
    hUopen.preimage (periodOnePotential (p := p)).continuous
  refine ⟨V, hVopen, hφU, B+1, by linarith, ?_⟩
  intro ψ hψ k
  let a := canonicalPeriodicLeftDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let b := canonicalPeriodicRightDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  obtain ⟨ha, hb, _⟩ := hdata (periodOnePotential ψ) hψ
    (periodOnePotential_mem ψ)
  have haPoint := lp.norm_apply_le_norm
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' a k
  have hbPoint := lp.norm_apply_le_norm
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' b k
  have hleft : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) k ∈ Metric.ball ((Real.pi : ℂ)*k) (B+1) := by
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖a k‖ < B+1
    linarith
  have hright : canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) k ∈ Metric.ball ((Real.pi : ℂ)*k) (B+1) := by
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖b k‖ < B+1
    linarith
  exact (convex_ball ((Real.pi : ℂ)*k) (B+1)).segment_subset hleft hright

/-- One source neighborhood and one index cutoff keep every distant
periodic gap segment outside a fixed unit spectral ball. -/
theorem exists_uniform_sourcePeriodicSegment_tail_avoids_ball
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (z₀ : ℂ) :
    ∃ N : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ k : ℤ, N < k.natAbs →
        Metric.ball z₀ 1 ⊆ (sourcePeriodicSegment hp hp1 ψ k)ᶜ := by
  obtain ⟨V, hVopen, hφV, R, _, hseg⟩ :=
    exists_uniform_sourcePeriodicSegment_freeBall hp hp1 φ
  obtain ⟨N, hN⟩ := exists_nat_gt ((‖z₀‖+1+R)/Real.pi)
  refine ⟨N, V, hVopen, hφV, ?_⟩
  intro ψ hψ k hk w hw hws
  have hwnear : ‖w-z₀‖ < 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hwseg : ‖w-((Real.pi : ℂ)*k)‖ < R := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hseg ψ hψ k hws
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

/-- Analytic symmetric gap data make avoidance of one moving periodic
segment stable in the joint spectral/source topology. -/
theorem exists_joint_neighborhood_avoids_sourcePeriodicSegment
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (z : ℂ) (n : ℤ)
    (hmid : AnalyticAt ℂ (fun χ : CoeffPair p =>
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential χ)
        (periodOnePotential_mem χ) n) φ)
    (hgap : AnalyticAt ℂ (fun χ : CoeffPair p =>
      (canonicalPeriodicGap hp hp1 (periodOnePotential χ)
        (periodOnePotential_mem χ) n)^2) φ)
    (hz : z ∉ sourcePeriodicSegment hp hp1 φ n) :
    ∃ U : Set (ℂ × CoeffPair p), IsOpen U ∧ (z,φ) ∈ U ∧
      ∀ t ∈ U, t.1 ∉ sourcePeriodicSegment hp hp1 t.2 n := by
  let a : ℂ × CoeffPair p → ℂ := fun t =>
    canonicalPeriodicLeft hp hp1 (periodOnePotential t.2)
      (periodOnePotential_mem t.2) n
  let b : ℂ × CoeffPair p → ℂ := fun t =>
    canonicalPeriodicRight hp hp1 (periodOnePotential t.2)
      (periodOnePotential_mem t.2) n
  have hsnd : ContinuousAt (fun t : ℂ × CoeffPair p => t.2) (z,φ) :=
    continuous_snd.continuousAt
  have hM : ContinuousAt (fun t : ℂ × CoeffPair p => (a t+b t)/2) (z,φ) := by
    change ContinuousAt (fun t : ℂ × CoeffPair p =>
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential t.2)
        (periodOnePotential_mem t.2) n) (z,φ)
    exact hmid.continuousAt.comp hsnd
  have hG : ContinuousAt (fun t : ℂ × CoeffPair p => (b t-a t)^2) (z,φ) := by
    change ContinuousAt (fun t : ℂ × CoeffPair p =>
      (canonicalPeriodicGap hp hp1 (periodOnePotential t.2)
        (periodOnePotential_mem t.2) n)^2) (z,φ)
    exact hgap.continuousAt.comp hsnd
  exact NLS.ComplexAnalysis.exists_open_avoids_segment_of_symmetric_continuousAt
    a b Prod.fst (z,φ) hz continuous_fst.continuousAt hM hG

/-- The moving-gap complement over a source set, expressed as a subset
of the joint spectral/source product space. -/
def sourceStandardRootPairedJointDomain (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) : Set (ℂ × CoeffPair p) :=
  {t | t.2 ∈ W ∧ t.1 ∈ sourceStandardRootPairedDomain hp hp1 t.2}

/-- Analytic symmetric gap coordinates on an open source set make its
joint moving-gap complement open. The source-uniform tail bound reduces
the infinitely many gaps to finitely many local incidence tests. -/
theorem isOpen_sourceStandardRootPairedJointDomain_of_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (hWopen : IsOpen W)
    (hA : ∀ ψ ∈ W, ∀ n : ℤ,
      AnalyticAt ℂ (fun χ : CoeffPair p =>
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential χ)
          (periodOnePotential_mem χ) n) ψ ∧
      AnalyticAt ℂ (fun χ : CoeffPair p =>
        (canonicalPeriodicGap hp hp1 (periodOnePotential χ)
          (periodOnePotential_mem χ) n)^2) ψ) :
    IsOpen (sourceStandardRootPairedJointDomain hp hp1 W) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨z,φ⟩ ⟨hφ, hz⟩
  obtain ⟨N, V, hVopen, hφV, htail⟩ :=
    exists_uniform_sourcePeriodicSegment_tail_avoids_ball hp hp1 φ z
  let s : Finset ℤ := (Finset.Icc (-(N : ℤ)) N).erase 0
  let A (k : ℤ) : Set (ℂ × CoeffPair p) :=
    {t | t.1 ∉ sourcePeriodicSegment hp hp1 t.2 k}
  have hfinite (k : ℤ) (hk : k ∈ s) : A k ∈ 𝓝 (z,φ) := by
    have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
    obtain ⟨U, hUopen, hbaseU, hUsub⟩ :=
      exists_joint_neighborhood_avoids_sourcePeriodicSegment hp hp1 φ z k
        (hA φ hφ k).1 (hA φ hφ k).2 (hz k hk0)
    exact Filter.mem_of_superset (hUopen.mem_nhds hbaseU) hUsub
  have hfinnear : (⋂ k ∈ s, A k) ∈ 𝓝 (z,φ) :=
    (Filter.biInter_finset_mem s).mpr hfinite
  have hWnear : {t : ℂ × CoeffPair p | t.2 ∈ W} ∈ 𝓝 (z,φ) :=
    (hWopen.preimage continuous_snd).mem_nhds hφ
  have hVnear : {t : ℂ × CoeffPair p | t.2 ∈ V} ∈ 𝓝 (z,φ) :=
    (hVopen.preimage continuous_snd).mem_nhds hφV
  have hballnear : {t : ℂ × CoeffPair p | t.1 ∈ Metric.ball z 1} ∈ 𝓝 (z,φ) :=
    (isOpen_ball.preimage continuous_fst).mem_nhds
      (mem_ball_self (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hWnear, hVnear, hballnear, hfinnear] with t htW htV htball htfin
  refine ⟨htW, ?_⟩
  intro k hk0
  by_cases hk : k ∈ s
  · exact (Set.mem_iInter.mp (Set.mem_iInter.mp htfin k) hk)
  · have hlarge : N < k.natAbs := by
      have hnotIcc : k ∉ Finset.Icc (-(N : ℤ)) N := by
        intro hIcc
        exact hk (Finset.mem_erase.mpr ⟨hk0, hIcc⟩)
      simp only [Finset.mem_Icc] at hnotIcc
      omega
    exact (htail t.2 htV k hlarge) htball

/-- One connected almost-real source domain has an open joint
moving-gap complement, on which every finite paired cutoff is analytic. -/
theorem exists_global_source_open_analytic_pairedJointDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      IsOpen (sourceStandardRootPairedJointDomain hp hp1 W) ∧
      ∀ N : ℕ, AnalyticOnNhd ℂ
        (sourceStandardRootPairedJointPartialProduct hp hp1 N)
        (sourceStandardRootPairedJointDomain hp hp1 W) := by
  obtain ⟨W, hWopen, hWconnected, hreal, hA⟩ :=
    exists_global_source_analytic_midpoint_squaredGap hp hp1
  refine ⟨W, hWopen, hWconnected, hreal,
    isOpen_sourceStandardRootPairedJointDomain_of_analytic hp hp1 W hWopen hA, ?_⟩
  intro N t ht
  have hroot (n : ℤ) (hn : t.1 ∉ sourcePeriodicSegment hp hp1 t.2 n) :
      AnalyticAt ℂ (fun q : ℂ × CoeffPair p =>
        sourceStandardRoot hp hp1 q.2 n q.1) t :=
    sourceStandardRoot_joint_analyticAt_of_symmetric hp hp1 t.2 n t.1
      (hA t.2 ht.1 n).1 (hA t.2 ht.1 n).2 hn
  change AnalyticAt ℂ (fun q : ℂ × CoeffPair p =>
    ∏ j ∈ Finset.range N, sourceStandardRootPairedFactor hp hp1 q.2 q.1 j) t
  exact (Finset.range N).analyticAt_fun_prod (fun j _ =>
    sourceStandardRootPairedFactor_joint_analyticAt hp hp1 t.2 t.1 ht.2 hroot j)

/-- On the same open joint domain as the analytic finite cutoffs,
the paired products converge locally uniformly to the actual infinite
product. -/
theorem exists_global_source_open_locallyUniform_pairedJointProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      IsOpen (sourceStandardRootPairedJointDomain hp hp1 W) ∧
      (∀ N : ℕ, AnalyticOnNhd ℂ
        (sourceStandardRootPairedJointPartialProduct hp hp1 N)
        (sourceStandardRootPairedJointDomain hp hp1 W)) ∧
      TendstoLocallyUniformlyOn
        (sourceStandardRootPairedJointPartialProduct hp hp1)
        (sourceStandardRootPairedJointProduct hp hp1) atTop
        (sourceStandardRootPairedJointDomain hp hp1 W) := by
  obtain ⟨W, hWopen, hWconnected, hreal, hDopen, hfinite⟩ :=
    exists_global_source_open_analytic_pairedJointDomain hp hp1
  refine ⟨W, hWopen, hWconnected, hreal, hDopen, hfinite, ?_⟩
  intro u hu t ht
  obtain ⟨U, hUopen, htU, hconv⟩ :=
    exists_local_uniform_sourceStandardRootPairedProduct hp hp1 t.2 t.1
      (fun N => (hfinite N t ht).continuousAt)
  refine ⟨U, mem_nhdsWithin_of_mem_nhds (hUopen.mem_nhds htU), ?_⟩
  exact hconv u hu

end NLS.ZakharovShabat
