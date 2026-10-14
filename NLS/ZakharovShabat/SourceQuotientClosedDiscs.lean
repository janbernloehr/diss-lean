import NLS.ZakharovShabat.SourceLemma10_7
import NLS.ComplexAnalysis.CompactParameterBounds

/-!
# Closed isolating disks and finite quotient bounds

Positive separation keeps the original closed disks in the omitted-root
domain. Compactness gives a common finite-head bound near every complex
source on the common domain and every numerator root displacement.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceIsolatingNeighborhoods.closedDisc_separation
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (i j : ℤ) (hij : i ≠ j) (z : ℂ) (hz : z ∈ closure (D i))
    (w : ℂ) (hw : w ∈ D j) :
    c⁻¹*|((i-j : ℤ) : ℝ)| ≤ dist z w := by
  have hclosed : IsClosed {x : ℂ | c⁻¹*|((i-j : ℤ) : ℝ)| ≤ dist x w} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  exact closure_minimal (fun x hx => (hD.pointwise_distance i j hij x hx w hw).1) hclosed hz

theorem SourceIsolatingNeighborhoods.closedDisc_subset_omittedDomain
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
    closure (D n) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n := by
  intro z hz m hm hseg
  have hd := hD.closedDisc_separation n m hm.symm z hz z (hD.gap ψ hψ m hseg)
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hD.one_le
  have hi : 0 < |((n-m : ℤ) : ℝ)| := by
    apply abs_pos.mpr
    exact_mod_cast sub_ne_zero.mpr hm.symm
  have hpos := mul_pos (inv_pos.mpr hc) hi
  simp only [dist_self] at hd
  linarith

theorem SourceIsolatingNeighborhoods.isCompact_closedDisc
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (n : ℤ) : IsCompact (closure (D n)) := by
  obtain ⟨a,r,hr,he⟩ := hD.discs n
  rw [he,closure_ball _ (ne_of_gt hr)]
  exact isCompact_closedBall _ _

/-- A generic finite head bound, with every original closed disk retained. -/
theorem SourceCorollary10_6Data.finiteClosedDiscBound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceCorollary10_6Data hp hp1 W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V) (a : Coeff p) (s : Finset ℤ) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a,φ) ∈ U ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ U, ∀ n ∈ s, ∀ z ∈ closure (D n),
        ‖sourceSingleRootQuotientJointProduct hp hp1 n (z,t)-1‖ ≤ M := by
  have hlocal (n : ℤ) :
      ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a,φ) ∈ U ∧
        ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ U, ∀ z ∈ closure (D n),
          ‖sourceSingleRootQuotientJointProduct hp hp1 n (z,t)-1‖ ≤ M := by
    let f : ℂ × (Coeff p × CoeffPair p) → ℂ := fun q =>
      sourceSingleRootQuotientJointProduct hp hp1 n q - 1
    have hf : ContinuousOn f (sourceSingleRootQuotientJointDomain hp hp1 W n) :=
      (h.joint n).2.continuousOn.sub continuousOn_const
    have hbase : ∀ z ∈ closure (D n),
        (z,(a,φ)) ∈ sourceSingleRootQuotientJointDomain hp hp1 W n := by
      intro z hz
      exact ⟨hφW,hD.closedDisc_subset_omittedDomain φ hφV n hz⟩
    obtain ⟨U,ho,ha,M,hM,hbound⟩ :=
      NLS.ComplexAnalysis.exists_local_uniform_bound_on_compact_of_continuousOn
        f _ (h.joint n).1 hf _ (hD.isCompact_closedDisc n) (a,φ) hbase
    exact ⟨U,ho,ha,M,hM,fun t ht z hz => (hbound t ht z hz).2⟩
  choose U ho ha M hM hbound using hlocal
  refine ⟨⋂ n ∈ s, U n,isOpen_biInter_finset (fun n _ => ho n),?_,
    ∑ n ∈ s, M n,Finset.sum_nonneg (fun n _ => hM n),?_⟩
  · simp only [mem_iInter]
    exact fun n _ => ha n
  · intro t ht n hn z hz
    simp only [mem_iInter] at ht
    exact (hbound n t (ht n hn) z hz).trans
      (Finset.single_le_sum (f := M) (fun k _ => hM k) hn)

end NLS.ZakharovShabat
