import NLS.ZakharovShabat.SourceQuotientAllDiscMajorants
import NLS.SequenceSpaces.TwoExponentDecomposition
import NLS.SequenceSpaces.RefinedOnePlusDecomposition

/-!
# The literal quotient supremum and its sequence decomposition

Every actual disk is nonempty and the supremum is finite. The q>1
estimate gives an exact lq + l(p/2) decomposition, including p/2<1.
At q=1 there is a single l(p/2) + l(1+) pair, chosen before any
projection exponent. Its bounds hold on bounded offset families.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The actual numerator-minus-midpoint displacement in the original source exponent. -/
def sourceNumeratorMidpointOffset (hp : p ≠ ⊤) (hp1 : 1 < p)
    (t : Coeff p × CoeffPair p) : Coeff p := t.1-sourcePeriodicMidpointDisplacement hp hp1 t.2

theorem sourceNumeratorMidpointOffset_apply (hp : p ≠ ⊤) (hp1 : 1 < p)
    (t : Coeff p × CoeffPair p) (m : ℤ) :
    displacedRoots t.1 m-
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential t.2) (periodOnePotential_mem t.2) m =
        sourceNumeratorMidpointOffset hp hp1 t m := by
  simp only [sourceNumeratorMidpointOffset,lp.coeFn_sub,Pi.sub_apply,
    sourcePeriodicMidpointDisplacement_apply,displacedRoots]
  ring

/-- The supremum appearing literally in Lemma 10.8. -/
def sourceQuotientDiscSup (hp : p ≠ ⊤) (hp1 : 1 < p) (D : ℤ → Set ℂ)
    (t : Coeff p × CoeffPair p) (n : ℤ) : ℝ :=
  sSup ((fun z => ‖sourceSingleRootQuotientJointProduct hp hp1 n (z,t)-1‖) '' D n)

/-- Parameters with an explicit bound in the offset exponent. -/
def sourceQuotientOffsetFamily (hp : p ≠ ⊤) (hp1 : 1 < p)
    (U : Set (Coeff p × CoeffPair p)) (T : ℝ) (q : ℝ≥0∞) :
    Set ((Coeff p × CoeffPair p) × Coeff q) :=
  {x | x.1 ∈ U ∧ ‖x.2‖ ≤ T ∧ ∀ m : ℤ, displacedRoots x.1.1 m-
    canonicalPeriodicMidpoint hp hp1 (periodOnePotential x.1.2) (periodOnePotential_mem x.1.2) m = x.2 m}

variable {hp : p ≠ ⊤} {hp1 : 1 < p} {U : Set (Coeff p × CoeffPair p)}
variable {D : ℤ → Set ℂ} {c R H M : ℝ} {N K : ℕ}

theorem SourceQuotientDiscEstimates.sup_bddAbove
    (h : SourceQuotientDiscEstimates hp hp1 U D c R H M N K)
    (t : Coeff p × CoeffPair p) (ht : t ∈ U) (n : ℤ) :
    BddAbove ((fun z => ‖sourceSingleRootQuotientJointProduct hp hp1 n (z,t)-1‖) '' D n) := by
  let α := sourceNumeratorMidpointOffset hp hp1 t
  obtain ⟨_,_,_,_,hb⟩ := h.majorants hp1 hp ‖α‖ (norm_nonneg _)
  obtain ⟨A,B,_,_,hpoint⟩ := hb t ht α le_rfl (sourceNumeratorMidpointOffset_apply hp hp1 t)
  refine ⟨‖A n‖+‖B n‖,?_⟩
  rintro y ⟨z,hz,rfl⟩
  exact hpoint n z hz

theorem SourceQuotientDiscEstimates.norm_le_sup
    (h : SourceQuotientDiscEstimates hp hp1 U D c R H M N K)
    (t : Coeff p × CoeffPair p) (ht : t ∈ U) (n : ℤ) (z : ℂ) (hz : z ∈ D n) :
    ‖sourceSingleRootQuotientJointProduct hp hp1 n (z,t)-1‖ ≤ sourceQuotientDiscSup hp hp1 D t n :=
  le_csSup (h.sup_bddAbove t ht n) ⟨z,hz,rfl⟩

theorem SourceQuotientDiscEstimates.sup_nonneg
    (h : SourceQuotientDiscEstimates hp hp1 U D c R H M N K)
    (t : Coeff p × CoeffPair p) (ht : t ∈ U) (n : ℤ) :
    0 ≤ sourceQuotientDiscSup hp hp1 D t n := by
  obtain ⟨z,hz⟩ := h.nonempty n
  exact (norm_nonneg _).trans (h.norm_le_sup t ht n z hz)

theorem SourceQuotientDiscEstimates.sup_le
    (h : SourceQuotientDiscEstimates hp hp1 U D c R H M N K)
    (t : Coeff p × CoeffPair p) (n : ℤ) (b : ℝ)
    (hb : ∀ z ∈ D n, ‖sourceSingleRootQuotientJointProduct hp hp1 n (z,t)-1‖ ≤ b) :
    sourceQuotientDiscSup hp hp1 D t n ≤ b := by
  apply csSup_le ((h.nonempty n).image _)
  rintro y ⟨z,hz,rfl⟩
  exact hb z hz

/-- An exact supremum decomposition with uniform separate norm bounds on each bounded offset family. -/
theorem SourceQuotientDiscEstimates.supDecomposition
    (h : SourceQuotientDiscEstimates hp hp1 U D c R H M N K)
    (hq1 : 1 < q) (hq : q ≠ ⊤) (T : ℝ) (hT : 0 ≤ T) :
    ∃ Lq Lg : ℝ, 0 ≤ Lq ∧ 0 ≤ Lg ∧
      ∀ x ∈ sourceQuotientOffsetFamily hp hp1 U T q,
        ∃ A : Coeff q, ∃ B : Coeff (ENNReal.ofReal (p.toReal/2)),
          (∀ n : ℤ, (sourceQuotientDiscSup hp hp1 D x.1 n : ℂ) = A n+B n) ∧
          ‖A‖ ≤ Lq ∧ ‖B‖ ≤ Lg := by
  obtain ⟨Lq,Lg,hLq,hLg,hbound⟩ := h.majorants hq1 hq T hT
  have hhalf : 0 < ENNReal.ofReal (p.toReal/2) := by
    have hpr := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
    exact ENNReal.ofReal_pos.mpr (by positivity)
  refine ⟨Lq,Lg,hLq,hLg,?_⟩
  intro x hx
  obtain ⟨A,B,hA,hB,hpoint⟩ := hbound x.1 hx.1 x.2 hx.2.1 hx.2.2
  obtain ⟨C,E,hCE,hC,hE⟩ := Coeff.exists_coeff_decomposition_of_twoSequenceMajorants hhalf
    (fun n => (sourceQuotientDiscSup hp hp1 D x.1 n : ℂ)) A B (by
      intro n
      rw [Complex.norm_real,Real.norm_of_nonneg (h.sup_nonneg x.1 hx.1 n)]
      exact h.sup_le x.1 n _ (hpoint n))
  exact ⟨C,E,fun n => (hCE n).symm,hC.trans hA,hE.trans hB⟩

/-- At the endpoint the two sequences are chosen before the l(1+) projection exponent. -/
theorem SourceQuotientDiscEstimates.supDecomposition_one
    (h : SourceQuotientDiscEstimates hp hp1 U D c R H M N K)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ A : ((Coeff p × CoeffPair p) × Coeff 1) → Coeff (ENNReal.ofReal (p.toReal/2)),
    ∃ B : ((Coeff p × CoeffPair p) × Coeff 1) → CoeffOnePlus,
      (∀ x ∈ sourceQuotientOffsetFamily hp hp1 U T 1, ∀ n : ℤ,
        (sourceQuotientDiscSup hp hp1 D x.1 n : ℂ) = A x n+(B x).1 n) ∧
      (∃ Lg : ℝ, 0 ≤ Lg ∧ ∀ x ∈ sourceQuotientOffsetFamily hp hp1 U T 1, ‖A x‖ ≤ Lg) ∧
      ∀ (r : ℝ≥0∞) (hr1 : 1 < r) (hr : r ≠ ⊤),
        ∃ Lr : ℝ, 0 ≤ Lr ∧ ∀ x ∈ sourceQuotientOffsetFamily hp hp1 U T 1,
          ‖CoeffOnePlus.toCoeff r hr1 hr (B x)‖ ≤ Lr := by
  have hhalf : 0 < ENNReal.ofReal (p.toReal/2) := by
    have hpr := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
    exact ENNReal.ofReal_pos.mpr (by positivity)
  apply Coeff.exists_onePlus_decomposition_of_refined
    (sourceQuotientOffsetFamily hp hp1 U T 1)
    (fun x n => (sourceQuotientDiscSup hp hp1 D x.1 n : ℂ)) (by simp)
  intro r hr hr1 hhalfr
  let : Fact (1 ≤ r) := ⟨hr1.le⟩
  obtain ⟨Lr,Lg,hLr,hLg,hbound⟩ := h.majorants_one hr1 hr T hT
  refine ⟨Lr+Lg,add_nonneg hLr hLg,?_⟩
  intro x hx
  obtain ⟨A,B,hA,hB,hpoint⟩ := hbound x.1 hx.1 x.2 hx.2.1 hx.2.2
  obtain ⟨C,hC,hCn,_⟩ := Coeff.exists_tailCoeff_of_twoSequenceMajorants
    hhalf hr1 hr hhalfr (fun n => (sourceQuotientDiscSup hp hp1 D x.1 n : ℂ)) 0 A B (by
      intro n _
      rw [Complex.norm_real,Real.norm_of_nonneg (h.sup_nonneg x.1 hx.1 n)]
      exact h.sup_le x.1 n _ (hpoint n))
  exact ⟨C,fun n => by simpa using hC n,hCn.trans (add_le_add hA hB)⟩

end NLS.ZakharovShabat
