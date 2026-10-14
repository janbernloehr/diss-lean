import NLS.ZakharovShabat.SourceQuotientOriginalTopology
import NLS.ComplexAnalysis.CompactSliceLocalBounds
import NLS.SequenceSpaces.SingleCoordinateCompact

/-!
# Quotient bounds on original disks for every filled deleted input

The original-domain quotient estimates are locally bounded uniformly in
the selected disk. Compactness of single-coordinate insertions makes the
bound uniform in an additional deleted index, without restricting the
finite coordinates of the arbitrary root input.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceCorollary10_6Data.local_allDisk_quotient_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V) (a : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a,φ) ∈ U ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ U, ∀ m : ℤ, ∀ z ∈ D m,
        ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,t)‖ ≤ C := by
  obtain ⟨U,ho,ha,_,R,G,M,N,K,h⟩ := H.quotientDiscEstimates hD hV φ hφW hφV a
  obtain ⟨A,B,hA,hB,hbound⟩ := h.supDecomposition_originalTopology a
  refine ⟨U ∩ (ball a 1 ×ˢ univ),ho.inter (isOpen_ball.prod isOpen_univ),
    ⟨ha,mem_ball_self (by norm_num),mem_univ _⟩,A+B+1,by positivity,?_⟩
  intro t ht m z hz
  obtain ⟨X,Y,he,hX,hY⟩ := hbound p le_rfl t ht
  have hp0 := (zero_lt_one.trans hp1).ne'
  have hhalf : 0 < ENNReal.ofReal (p.toReal/2) :=
    ENNReal.ofReal_pos.mpr (by
      have := ENNReal.toReal_pos hp0 hp
      positivity)
  have hsup : sourceQuotientDiscSup hp hp1 D t m ≤ A+B := by
    have hn : ‖(sourceQuotientDiscSup hp hp1 D t m : ℂ)‖ ≤ A+B := by
      rw [he]
      exact (norm_add_le _ _).trans (add_le_add
        ((lp.norm_apply_le_norm hp0 X m).trans hX)
        ((lp.norm_apply_le_norm hhalf.ne' Y m).trans hY))
    simpa only [Complex.norm_real,Real.norm_of_nonneg (h.sup_nonneg t ht.1 m)] using hn
  have hb := (h.norm_le_sup t ht.1 m z hz).trans hsup
  calc
    ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,t)‖ ≤
        ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,t)-1‖+1 := by
      simpa using norm_le_norm_sub_add (sourceSingleRootQuotientJointProduct hp hp1 m (z,t)) 1
    _ ≤ A+B+1 := by linarith

/-- One original-domain neighborhood bounds every quotient after any
single-coordinate insertion from a fixed finite-exponent sequence. -/
theorem SourceCorollary10_6Data.local_filled_allDisk_quotient_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (a b : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a,φ) ∈ U ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ U, ∀ n m : ℤ, ∀ z ∈ D m,
        ‖sourceSingleRootQuotientJointProduct hp hp1 m
          (z,(t.1+lp.single p n (b n),t.2))‖ ≤ C := by
  obtain ⟨K,hK,_,hins⟩ := Coeff.exists_compact_single_insertions hp b
  let f : Coeff p × (Coeff p × CoeffPair p) → (Σ m : ℤ, D m) → ℝ :=
    fun q j => ‖sourceSingleRootQuotientJointProduct hp hp1 j.1
      (j.2,(q.2.1+q.1,q.2.2))‖
  obtain ⟨U,hU,hbase,C,hC,hbound⟩ := NLS.ComplexAnalysis.exists_uniform_bound_near_compact_slice
    K hK (a,φ) f (by
      intro v _
      obtain ⟨O,hO,hbase,L,hL,hb⟩ := H.local_allDisk_quotient_bound hD hV φ hφW hφV (a+v)
      let g : Coeff p × (Coeff p × CoeffPair p) → Coeff p × CoeffPair p :=
        fun q => (q.2.1+q.1,q.2.2)
      have hg : Continuous g := by fun_prop
      exact ⟨g ⁻¹' O,hO.preimage hg,hbase,L,hL,
        fun q hq j => hb (g q) hq j.1 j.2 j.2.property⟩)
  exact ⟨U,hU,hbase,C,hC,fun t ht n m z hz => hbound t ht _ (hins n) ⟨m,⟨z,hz⟩⟩⟩

end NLS.ZakharovShabat
