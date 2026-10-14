import NLS.ZakharovShabat.SourceIsolatingDiscDistance

/-!
# Lemma 10.1 on the almost-real source domain

One common sequence of real-centered discs isolates all nearby spectral
clusters, with the literal infimum-distance bounds (2.7) and the exact free
tail. The local neighborhoods form an open connected neighborhood of the
entire real-type locus. This is the domain used by the source proof; the
printed statement's complex-type subscript is recorded separately in the
source audit.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A common isolating family with all three source conditions and real centers. -/
structure SourceIsolatingNeighborhoods (hp : p ≠ ⊤) (hp1 : 1 < p)
    (V : Set (CoeffPair p)) (D : ℤ → Set ℂ) (c : ℝ) : Prop where
  one_le : 1 ≤ c
  discs : ∀ n, ∃ a r : ℝ, 0 < r ∧ D n = ball (a : ℂ) r
  cluster : ∀ ψ ∈ V, ∀ n, sourceSpectralCluster hp hp1 ψ n ⊆ D n
  gap : ∀ ψ ∈ V, ∀ n, sourcePeriodicSegment hp hp1 ψ n ⊆ D n
  pointwise_distance : ∀ i j : ℤ, i ≠ j → ∀ z ∈ D i, ∀ w ∈ D j,
    c⁻¹*|((i-j : ℤ) : ℝ)| ≤ dist z w ∧ dist z w ≤ c*|((i-j : ℤ) : ℝ)|
  set_distance : ∀ i j : ℤ, i ≠ j →
    c⁻¹*|((i-j : ℤ) : ℝ)| ≤ spectralSetDistance (D i) (D j) ∧
      spectralSetDistance (D i) (D j) ≤ c*|((i-j : ℤ) : ℝ)|
  tail : ∃ N : ℕ, ∀ n : ℤ, N < n.natAbs → D n = refinedResonantDisk n

/-- The quantitative lower bound implies disjointness at every distinct index. -/
theorem SourceIsolatingNeighborhoods.disjoint {hp : p ≠ ⊤} {hp1 : 1 < p}
    {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (h : SourceIsolatingNeighborhoods hp hp1 V D c) (i j : ℤ) (hij : i ≠ j) :
    Disjoint (D i) (D j) := by
  apply Set.disjoint_left.mpr
  intro z hz hw
  have hd := (h.pointwise_distance i j hij z hz z hw).1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one h.one_le
  have ht : 0 < |((i-j : ℤ) : ℝ)| := by
    apply abs_pos.mpr
    exact_mod_cast sub_ne_zero.mpr hij
  have hpos : 0 < c⁻¹*|((i-j : ℤ) : ℝ)| := mul_pos (inv_pos.mpr hc) ht
  simp only [dist_self] at hd
  linarith

/-- A real base admits a common family with quantitative separation and an open connected source neighborhood. -/
theorem exists_local_source_quantitative_isolating_discs
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∃ c : ℝ, SourceIsolatingNeighborhoods hp hp1 V (sourceIsolatingDisc hp hp1 φ N ε) c := by
  obtain ⟨N,ε,hε,hεmax,U,hUopen,hφU,hcluster,hdisjoint⟩ :=
    exists_local_source_pairwise_disjoint_isolating_discs hp hp1 φ hφ
  have hevent : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        sourceSpectralCluster hp hp1 ψ n ⊆ sourceClusterDisc hp hp1 φ (fun _ => ε/2) n := by
    rw [Finset.eventually_all]
    intro n hn
    exact eventually_sourceSpectralCluster_subset_open hp hp1 φ hφ n _ isOpen_ball
      (sourceSpectralCluster_subset_disc hp hp1 φ hφ (fun _ => ε/2) n (by positivity))
  obtain ⟨Uc,hUcsub,hUcopen,hφUc⟩ := _root_.mem_nhds_iff.mp hevent
  have hlocal : ∀ ψ ∈ U ∩ Uc, ∀ n : ℤ,
      sourceSpectralCluster hp hp1 ψ n ⊆ sourceIsolatingDisc hp hp1 φ N (ε/2) n := by
    intro ψ hψ n
    by_cases hn : n.natAbs ≤ N
    · simp only [sourceIsolatingDisc,if_pos hn]
      exact hUcsub hψ.2 n (by simp only [Finset.mem_Icc]; omega)
    · simpa only [sourceIsolatingDisc,if_neg hn] using hcluster ψ hψ.1 n
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp ((hUopen.inter hUcopen).mem_nhds ⟨hφU,hφUc⟩)
  obtain ⟨c,hc,hpoint⟩ := exists_source_shrunk_isolating_pointwise_comparison hp hp1 φ N ε
    hε hεmax hdisjoint
  have hehalf : 0 < ε/2 := by positivity
  have hsmall : ∀ ψ ∈ ball φ r, ∀ n : ℤ,
      sourceSpectralCluster hp hp1 ψ n ⊆ sourceIsolatingDisc hp hp1 φ N (ε/2) n :=
    fun ψ hψ => hlocal ψ (hrV hψ)
  refine ⟨N,ε/2,hehalf,by linarith,ball φ r,isOpen_ball,isConnected_ball hr,
    mem_ball_self hr,c,hc,?_,hsmall,?_,hpoint,?_,N,?_⟩
  · intro n
    refine ⟨(sourceIsolatingCenter hp hp1 φ N n).re,sourceIsolatingRadius hp hp1 φ N (ε/2) n,
      sourceIsolatingRadius_pos hp hp1 φ N (ε/2) hehalf n,?_⟩
    have he : ((sourceIsolatingCenter hp hp1 φ N n).re : ℂ) = sourceIsolatingCenter hp hp1 φ N n := by
      simpa only [sourceIsolatingCenter_im_eq_zero,Complex.ofReal_zero,zero_mul,add_zero] using
        Complex.re_add_im (sourceIsolatingCenter hp hp1 φ N n)
    rw [he,sourceIsolatingDisc_eq_ball]
  · intro ψ hψ n
    exact sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ ψ N (ε/2) n (hsmall ψ hψ n)
  · exact spectralSetDistance_comparison_of_pointwise _
      (sourceIsolatingDisc_nonempty hp hp1 φ N (ε/2) hehalf) c hpoint
  · intro n hn
    simp only [sourceIsolatingDisc,if_neg (not_le.mpr hn)]

/-- Lemma 10.1 on the real-type locus specified by its proof, with the full distance condition (2.7). -/
theorem sourceLemma10_1 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ ψ ∈ V ∧ V ⊆ W ∧
        ∃ φ : CoeffPair p, IsRealType (CoeffPair.toMax p φ) ∧
          ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧ ∃ c : ℝ,
            SourceIsolatingNeighborhoods hp hp1 V (sourceIsolatingDisc hp hp1 φ N ε) c := by
  classical
  let R := {φ : CoeffPair p // φ ∈ realTypeSourceLocus p}
  have hloc (x : R) := exists_local_source_quantitative_isolating_discs hp hp1 x.val x.property
  choose N ε hε hεmax V hopen hconn hbase c hdata using hloc
  let W : Set (CoeffPair p) := ⋃ x : R, V x
  have hR : realTypeSourceLocus p ⊆ W := by
    intro φ hφ
    exact mem_iUnion_of_mem (⟨φ,hφ⟩ : R) (hbase ⟨φ,hφ⟩)
  have hWconn : IsConnected W := by
    have hspine := isConnected_realTypeSourceLocus (p := p)
    have hfamily (x : R) : IsConnected (realTypeSourceLocus p ∪ V x) :=
      hspine.union ⟨x.val,x.property,hbase x⟩ (hconn x)
    have hcommon : (⋂ x : R, realTypeSourceLocus p ∪ V x).Nonempty := by
      obtain ⟨φ,hφ⟩ := hspine.nonempty
      exact ⟨φ,mem_iInter.mpr (fun _ => Or.inl hφ)⟩
    have heq : (⋃ x : R, realTypeSourceLocus p ∪ V x) = W := by
      apply Set.Subset.antisymm
      · intro φ hφ
        obtain ⟨x,hx⟩ := mem_iUnion.mp hφ
        exact hx.elim (fun hr => hR hr) (fun hv => mem_iUnion_of_mem x hv)
      · intro φ hφ
        obtain ⟨x,hx⟩ := mem_iUnion.mp hφ
        exact mem_iUnion_of_mem x (Or.inr hx)
    refine ⟨hspine.nonempty.mono hR,?_⟩
    rw [← heq]
    exact isPreconnected_iUnion hcommon (fun x => (hfamily x).isPreconnected)
  refine ⟨W,isOpen_iUnion hopen,hWconn,hR,?_⟩
  intro ψ hψ
  obtain ⟨x,hx⟩ := mem_iUnion.mp hψ
  exact ⟨V x,hopen x,hconn x,hx,(fun χ hχ => mem_iUnion_of_mem x hχ),
    x.val,x.property,N x,ε x,hε x,hεmax x,c x,hdata x⟩

end NLS.ZakharovShabat
