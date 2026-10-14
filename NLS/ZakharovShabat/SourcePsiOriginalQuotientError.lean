import NLS.ZakharovShabat.SourcePsiOriginalQuotientBound
import NLS.SequenceSpaces.TwoExponentMajorant
import NLS.SequenceSpaces.DeletedOperatorExtension

/-!
# Uniform sequence bounds for the original quotient errors

The actual disk suprema form an lp sequence locally bounded in the original
parameters. Compact single-coordinate insertions make the bound uniform
in the inserted index, including when p/2 is below one.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceCorollary10_6Data.local_allDisk_quotient_errorBound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V) (a : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a,φ) ∈ U ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ U, ∃ E : Coeff p, ‖E‖ ≤ C ∧
        (∀ m : ℤ, E m = (sourceQuotientDiscSup hp hp1 D t m : ℂ)) ∧
        ∀ m : ℤ, ∀ z ∈ D m, ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,t)-1‖ ≤ ‖E m‖ := by
  obtain ⟨U,ho,ha,_,R,G,M,N,K,h⟩ := H.quotientDiscEstimates hD hV φ hφW hφV a
  obtain ⟨A,B,hA,hB,hbound⟩ := h.supDecomposition_originalTopology a
  have hhalf : 0 < ENNReal.ofReal (p.toReal/2) := by
    have := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hhalf_le : ENNReal.ofReal (p.toReal/2) ≤ p := by
    calc
      _ ≤ ENNReal.ofReal p.toReal := ENNReal.ofReal_le_ofReal (by linarith [ENNReal.toReal_nonneg (a := p)])
      _ = p := ENNReal.ofReal_toReal hp
  refine ⟨U ∩ (ball a 1 ×ˢ univ),ho.inter (isOpen_ball.prod isOpen_univ),
    ⟨ha,mem_ball_self (by norm_num),mem_univ _⟩,A+B,add_nonneg hA hB,?_⟩
  intro t ht
  obtain ⟨X,Y,he,hX,hY⟩ := hbound p le_rfl t ht
  obtain ⟨E,hE,hEn,_⟩ := Coeff.exists_tailCoeff_of_twoSequenceMajorants hhalf hp1 hp hhalf_le
    (fun m => (sourceQuotientDiscSup hp hp1 D t m : ℂ)) 0 X Y (by
      intro m _
      rw [he]
      exact norm_add_le _ _)
  have hval (m : ℤ) : E m = (sourceQuotientDiscSup hp hp1 D t m : ℂ) := by simpa using hE m
  refine ⟨E,hEn.trans (add_le_add hX hY),hval,?_⟩
  intro m z hz
  rw [hval,Complex.norm_real,Real.norm_of_nonneg (h.sup_nonneg t ht.1 m)]
  exact h.norm_le_sup t ht.1 m z hz

theorem SourceCorollary10_6Data.local_filled_allDisk_quotient_errorBound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (a b : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a,φ) ∈ U ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ U, ∀ n : ℤ, ∃ E : Coeff p, ‖E‖ ≤ C ∧
        (∀ m : ℤ, E m = (sourceQuotientDiscSup hp hp1 D (t.1+lp.single p n (b n),t.2) m : ℂ)) ∧
        ∀ m : ℤ, ∀ z ∈ D m,
          ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,(t.1+lp.single p n (b n),t.2))-1‖ ≤ ‖E m‖ := by
  obtain ⟨K,hK,_,hins⟩ := Coeff.exists_compact_single_insertions hp b
  let g : Coeff p × (Coeff p × CoeffPair p) → Coeff p × CoeffPair p :=
    fun q => (q.2.1+q.1,q.2.2)
  have hg : Continuous g := by fun_prop
  let P := fun (q : Coeff p × (Coeff p × CoeffPair p)) (C : ℝ) =>
    ∃ E : Coeff p, ‖E‖ ≤ C ∧
      (∀ m : ℤ, E m = (sourceQuotientDiscSup hp hp1 D (g q) m : ℂ)) ∧
      ∀ m : ℤ, ∀ z ∈ D m, ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,g q)-1‖ ≤ ‖E m‖
  obtain ⟨U,hU,hbase,C,hC,hbound⟩ := NLS.ComplexAnalysis.exists_uniform_property_near_compact_slice
    K hK (a,φ) P (by
      rintro q C L hCL ⟨E,hE,he,hb⟩
      exact ⟨E,hE.trans hCL,he,hb⟩) (by
      intro v _
      obtain ⟨O,hO,hbase,L,hL,hb⟩ := H.local_allDisk_quotient_errorBound hD hV φ hφW hφV (a+v)
      exact ⟨g ⁻¹' O,hO.preimage hg,hbase,L,hL,fun q hq => hb (g q) hq⟩)
  exact ⟨U,hU,hbase,C,hC,fun t ht n => hbound t ht _ (hins n)⟩

/-- Replacing any one coordinate by a fixed sequence value, rather than
adding that value, is uniformly controlled near an arbitrary full input. -/
theorem SourceCorollary10_6Data.local_replaced_allDisk_quotient_errorBound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (a b : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a,φ) ∈ U ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ U, ∀ n : ℤ, ∃ E : Coeff p, ‖E‖ ≤ C ∧
        (∀ m : ℤ, E m = (sourceQuotientDiscSup hp hp1 D
          (Coeff.deleteCoordinate n t.1+lp.single p n (b n),t.2) m : ℂ)) ∧
        ∀ m : ℤ, ∀ z ∈ D m, ‖sourceSingleRootQuotientJointProduct hp hp1 m
          (z,(Coeff.deleteCoordinate n t.1+lp.single p n (b n),t.2))-1‖ ≤ ‖E m‖ := by
  obtain ⟨U,hU,hbase,C,hC,hbound⟩ := H.local_filled_allDisk_quotient_errorBound hD hV φ hφW hφV a (b-a)
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU (a,φ) hbase
  refine ⟨ball (a,φ) ε,isOpen_ball,mem_ball_self hε,C,hC,?_⟩
  intro t ht n
  have hc : ‖Coeff.deleteCoordinate n (t.1-a)‖ ≤ ‖t.1-a‖ := by
    change ‖Coeff.deleteCoordinateTo n (t.1-a)‖ ≤ _
    exact ((Coeff.deleteCoordinateTo (p := p) n).le_opNorm _).trans
      (by simpa using mul_le_mul_of_nonneg_right (Coeff.norm_deleteCoordinateTo_le_one (p := p) n) (norm_nonneg (t.1-a)))
  have ht' : (a+Coeff.deleteCoordinate n (t.1-a),t.2) ∈ U := by
    apply hball
    rw [mem_ball]
    apply lt_of_le_of_lt ?_ (mem_ball.mp ht)
    simp only [dist_eq_norm]
    change max ‖a+Coeff.deleteCoordinate n (t.1-a)-a‖ ‖t.2-φ‖ ≤ max ‖t.1-a‖ ‖t.2-φ‖
    rw [add_sub_cancel_left]
    exact max_le_max hc le_rfl
  have he : a+Coeff.deleteCoordinate n (t.1-a)+lp.single p n ((b-a) n) =
      Coeff.deleteCoordinate n t.1+lp.single p n (b n) := by
    ext k
    by_cases hk : k = n
    · subst k
      simp only [lp.coeFn_add,Pi.add_apply,Coeff.deleteCoordinate_apply_same,
        lp.single_apply_self,lp.coeFn_sub,Pi.sub_apply]
      ring
    · simp only [lp.coeFn_add,Pi.add_apply,Coeff.deleteCoordinate_apply_other n k hk,
        lp.single_apply_ne _ _ _ hk,lp.coeFn_sub,Pi.sub_apply]
      ring
  simpa only [he] using hbound (a+Coeff.deleteCoordinate n (t.1-a),t.2) ht' n

end NLS.ZakharovShabat
