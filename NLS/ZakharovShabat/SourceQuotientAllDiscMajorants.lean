import NLS.ZakharovShabat.SourceQuotientAsymptoticGeometry
import NLS.ZakharovShabat.CompleteParityDisplacementBounds

/-!
# Quotient majorants on every original isolating disk

The finite central disks are filled using their common compact bound.
The two sequence exponents and the dependence on the numerator-minus-
midpoint norm remain explicit, including the endpoint q=1.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {U : Set (Coeff p × CoeffPair p)}
variable {D : ℤ → Set ℂ} {c R H M : ℝ} {N K : ℕ}

theorem SourceQuotientDiscEstimates.fillHead
    (h : SourceQuotientDiscEstimates hp hp1 U D c R H M N K)
    {r : ℝ≥0∞} (t : Coeff p × CoeffPair p) (ht : t ∈ U)
    (A : Coeff q) (B : Coeff r)
    (hbound : ∀ n : ℤ, K ≤ n.natAbs → ∀ z ∈ D n,
      ‖sourceSingleRootQuotientJointProduct hp hp1 n (z,t)-1‖ ≤ ‖A n‖+‖B n‖) :
    ∃ C : Coeff q, ‖C‖ ≤ (Finset.Icc (-(K:ℤ)) K).card*M+‖A‖ ∧
      ∀ n : ℤ, ∀ z ∈ D n,
        ‖sourceSingleRootQuotientJointProduct hp hp1 n (z,t)-1‖ ≤ ‖C n‖+‖B n‖ := by
  let s := Finset.Icc (-(K:ℤ)) K
  let f : ℤ → ℂ := fun n => if n ∈ s then (M:ℂ) else A n
  have hf : Memℓp f q := memℓp_of_eq_outside_finset (lp.memℓp A) s
    (by intro n hn; simp [f,hn])
  let C : Coeff q := ⟨f,hf⟩
  have hc (n : ℤ) (hn : n ∈ s) : ‖C n‖ = M := by
    simp only [C,f,if_pos hn,Complex.norm_real,Real.norm_of_nonneg h.head_nonneg]
  have he (n : ℤ) (hn : n ∉ s) : C n = A n := by simp [C,f,hn]
  refine ⟨C,Coeff.norm_le_of_eq_outside_finset C A s M (fun n hn => (hc n hn).le) he,?_⟩
  intro n z hz
  by_cases hn : n ∈ s
  · rw [hc n hn]
    have hh := h.head t ht n (by simp only [s,Finset.mem_Icc] at hn; omega) z (subset_closure hz)
    exact hh.trans (le_add_of_nonneg_right (norm_nonneg _))
  · rw [he n hn]
    exact hbound n (by simp only [s,Finset.mem_Icc] at hn; omega) z hz

/-- The same joint neighborhood works for every finite q>1 and every bounded lq offset family. -/
theorem SourceQuotientDiscEstimates.majorants
    (h : SourceQuotientDiscEstimates hp hp1 U D c R H M N K)
    (hq1 : 1 < q) (hq : q ≠ ⊤) (T : ℝ) (hT : 0 ≤ T) :
    ∃ Lq Lg : ℝ, 0 ≤ Lq ∧ 0 ≤ Lg ∧
      ∀ t ∈ U, ∀ α : Coeff q, ‖α‖ ≤ T →
        (∀ m : ℤ, displacedRoots t.1 m-
          canonicalPeriodicMidpoint hp hp1 (periodOnePotential t.2) (periodOnePotential_mem t.2) m = α m) →
        ∃ A : Coeff q, ∃ B : Coeff (ENNReal.ofReal (p.toReal/2)),
          ‖A‖ ≤ Lq ∧ ‖B‖ ≤ Lg ∧ ∀ n : ℤ, ∀ z ∈ D n,
            ‖sourceSingleRootQuotientJointProduct hp hp1 n (z,t)-1‖ ≤ ‖A n‖+‖B n‖ := by
  let u := Real.pi⁻¹*(Fourier.hilbertTransformBound hq1 hq+‖Fourier.hilbertSquareCoeffs‖)+
    c*R*‖Fourier.hilbertSquareCoeffs‖
  let d := (c/2)*Fourier.absoluteSampledRowConstant hq
  let v := ‖Coeff.puncturedLattice q.conjExponent
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖
  have hpr : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  let w := ‖squaredReciprocalKernel (min 1 (p.toReal/2))
    (lt_min (by norm_num : (1/2:ℝ)<1) (by linarith))‖
  have hc : 0 ≤ c := le_trans zero_le_one h.one_le
  have hu : 0 ≤ u := by
    have := Fourier.hilbertTransformBound_nonneg hq1 hq
    have := h.midpoint_nonneg
    dsimp [u]; positivity
  have hd : 0 ≤ d := by
    have := Fourier.absoluteSampledRowConstant_nonneg hq
    dsimp [d]; positivity
  have hv : 0 ≤ v := lp.norm_nonneg' _
  have hw : 0 ≤ w := lp.norm_nonneg' _
  let L := u*T+Real.exp (d*T)*(d*T)^2
  let G := (Real.exp (c*T*v)*c^2)*(H^2*w)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  refine ⟨(Finset.Icc (-(K:ℤ)) K).card*M+L,G,
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) h.head_nonneg) hL,hG,?_⟩
  intro t ht α hαT hα
  have hdom (n : ℤ) (hn : K ≤ n.natAbs) (z : ℂ)
      (hz : z ∈ sourceIsolatingDisc hp hp1 (0 : CoeffPair p) N 0 n) :
      (z,(t.1,t.2)) ∈ sourceSingleRootQuotientJointDomain hp hp1 univ n := by
    refine ⟨mem_univ _,h.domain t ht n z ?_⟩
    rw [h.tail n (h.threshold.trans_le hn)]
    simpa only [sourceIsolatingDisc,if_neg (not_le.mpr (h.threshold.trans_le hn))] using hz
  obtain ⟨A,B,hpoint,hA,hB⟩ := exists_sourceSingleRootQuotientDiscMajorants
    hp hp1 hq1 hq 0 t.2 t.1 α hα N K 0 c R h.one_le h.midpoint_nonneg
      (h.midpoint t ht) (h.separation t ht) hdom (h.small t ht)
  have hAn : ‖A‖ ≤ L := by
    apply hA.trans
    change u*‖α‖+Real.exp (d*‖α‖)*(d*‖α‖)^2 ≤ L
    dsimp [L]
    gcongr
  have hBn : ‖B‖ ≤ G := by
    have hg0 := lp.norm_nonneg' (sourcePeriodicSquaredGapCoeff hp hp1 t.2)
    have hg := h.squared_gap t ht
    apply hB.trans
    change (Real.exp (c*‖α‖*v)*c^2)*(‖sourcePeriodicSquaredGapCoeff hp hp1 t.2‖*w) ≤ G
    dsimp [G]
    gcongr
  obtain ⟨A',hA',hpoint'⟩ := h.fillHead t ht A B (by
    intro n hn z hz
    have hNn := h.threshold.trans_le hn
    apply hpoint n (by omega) z
    simpa only [sourceIsolatingDisc,if_neg (not_le.mpr hNn),← h.tail n hNn] using hz)
  exact ⟨A',B,hA'.trans (add_le_add le_rfl hAn),hBn,hpoint'⟩

/-- At q=1, all projection exponents use the same neighborhood and the same disks. -/
theorem SourceQuotientDiscEstimates.majorants_one
    (h : SourceQuotientDiscEstimates hp hp1 U D c R H M N K)
    (hq1 : 1 < q) (hq : q ≠ ⊤) (T : ℝ) (hT : 0 ≤ T) :
    ∃ Lq Lg : ℝ, 0 ≤ Lq ∧ 0 ≤ Lg ∧
      ∀ t ∈ U, ∀ α : Coeff 1, ‖α‖ ≤ T →
        (∀ m : ℤ, displacedRoots t.1 m-
          canonicalPeriodicMidpoint hp hp1 (periodOnePotential t.2) (periodOnePotential_mem t.2) m = α m) →
        ∃ A : Coeff q, ∃ B : Coeff (ENNReal.ofReal (p.toReal/2)),
          ‖A‖ ≤ Lq ∧ ‖B‖ ≤ Lg ∧ ∀ n : ℤ, ∀ z ∈ D n,
            ‖sourceSingleRootQuotientJointProduct hp hp1 n (z,t)-1‖ ≤ ‖A n‖+‖B n‖ := by
  obtain ⟨Lq,Lg,hLq,hLg,hbound⟩ := h.majorants hq1 hq T hT
  refine ⟨Lq,Lg,hLq,hLg,?_⟩
  intro t ht α hαT hα
  exact hbound t ht (Coeff.exponentInclusion hq1.le α)
    ((Coeff.norm_exponentInclusion_le hq1.le α).trans hαT) hα

end NLS.ZakharovShabat
