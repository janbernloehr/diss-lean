import NLS.ZakharovShabat.SourceQuotientDiscSupDecomposition
import NLS.ZakharovShabat.SourceFreeSineQuotientAsymptotic

/-!
# Local uniformity in the original root topology

For q>=p, including q=infinity, the offset norm is automatically locally
bounded in the original lp parameter topology. The free numerator uses
q=p without extra assumptions. Its filled sine quotient is retained at
the removable free center.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {U : Set (Coeff p × CoeffPair p)}
variable {D : ℤ → Set ℂ} {c R H M : ℝ} {N K : ℕ}

/-- In the original lp topology, every q>=p has locally uniform bounds on the same joint neighborhood. -/
theorem SourceQuotientDiscEstimates.supDecomposition_originalTopology
    (h : SourceQuotientDiscEstimates hp hp1 U D c R H M N K) (a : Coeff p) :
    ∃ Lp Lg : ℝ, 0 ≤ Lp ∧ 0 ≤ Lg ∧
      ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], p ≤ q →
        ∀ t ∈ U ∩ (ball a 1 ×ˢ univ),
          ∃ A : Coeff q, ∃ B : Coeff (ENNReal.ofReal (p.toReal/2)),
            (∀ n : ℤ, (sourceQuotientDiscSup hp hp1 D t n : ℂ) = A n+B n) ∧
            ‖A‖ ≤ Lp ∧ ‖B‖ ≤ Lg := by
  let T := ‖a‖+1+R
  have hT : 0 ≤ T := by have := h.midpoint_nonneg; dsimp [T]; positivity
  obtain ⟨Lp,Lg,hLp,hLg,hbound⟩ := h.supDecomposition hp1 hp T hT
  refine ⟨Lp,Lg,hLp,hLg,?_⟩
  intro q hqFact hpq t ht
  have hta : ‖t.1-a‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using ht.2.1
  have htn : ‖t.1‖ ≤ ‖a‖+1 := by
    have he : t.1 = (t.1-a)+a := by abel
    calc
      ‖t.1‖ = ‖(t.1-a)+a‖ := congrArg norm he
      _ ≤ ‖t.1-a‖+‖a‖ := norm_add_le _ _
      _ ≤ ‖a‖+1 := by linarith
  let α := sourceNumeratorMidpointOffset hp hp1 t
  have hα : ‖α‖ ≤ T :=
    (norm_sub_le t.1 (sourcePeriodicMidpointDisplacement hp hp1 t.2)).trans
      (add_le_add htn (h.midpoint t ht.1))
  obtain ⟨A,B,he,hA,hB⟩ := hbound (t,α)
    ⟨ht.1,hα,sourceNumeratorMidpointOffset_apply hp hp1 t⟩
  exact ⟨Coeff.exponentInclusion hpq A,B,he,
    (Coeff.norm_exponentInclusion_le hpq A).trans hA,hB⟩

/-- Exact agreement with the literal product on every selected disk. -/
theorem SourceQuotientDiscEstimates.product_eq
    (h : SourceQuotientDiscEstimates hp hp1 U D c R H M N K)
    (t : Coeff p × CoeffPair p) (ht : t ∈ U) (n : ℤ) (z : ℂ) (hz : z ∈ D n) :
    (∏' m : {m : ℤ // m ≠ n}, (displacedRoots t.1 m-z)/sourceStandardRoot hp hp1 t.2 m z) =
      sourceSingleRootQuotientJointProduct hp hp1 n (z,t) :=
  (hasProd_sourceSingleRootQuotient_subtype hp hp1 t.2 t.1 z n (h.domain t ht n z hz)).tprod_eq

/-- The free-numerator version of the same literal supremum. -/
theorem sourceQuotientDiscSup_free_eq (hp : p ≠ ⊤) (hp1 : 1 < p)
    (D : ℤ → Set ℂ) (ψ : CoeffPair p) (n : ℤ) :
    sourceQuotientDiscSup hp hp1 D (0,ψ) n =
      sSup ((fun z => ‖freeSineQuotient n z /
        sourceStandardRootOmittedJointProduct hp hp1 n (z,ψ)-1‖) '' D n) := by
  unfold sourceQuotientDiscSup
  simp only [sourceSingleRootQuotientJointProduct_free_eq_sine_div]

/-- The free-sine consequence is locally uniform with q=p on every original disk. -/
theorem SourceQuotientDiscEstimates.freeSineSupDecomposition
    (h : SourceQuotientDiscEstimates hp hp1 U D c R H M N K) :
    ∃ Lp Lg : ℝ, 0 ≤ Lp ∧ 0 ≤ Lg ∧
      ∀ ψ : CoeffPair p, (0,ψ) ∈ U →
        ∃ A : Coeff p, ∃ B : Coeff (ENNReal.ofReal (p.toReal/2)),
          (∀ n : ℤ, ((sSup ((fun z => ‖freeSineQuotient n z /
            sourceStandardRootOmittedJointProduct hp hp1 n (z,ψ)-1‖) '' D n) : ℝ) : ℂ) = A n+B n) ∧
          ‖A‖ ≤ Lp ∧ ‖B‖ ≤ Lg := by
  obtain ⟨Lp,Lg,hLp,hLg,hbound⟩ := h.supDecomposition hp1 hp R h.midpoint_nonneg
  refine ⟨Lp,Lg,hLp,hLg,?_⟩
  intro ψ hψ
  let α := sourceFreeNumeratorMidpointDisplacement hp hp1 ψ
  have hα : ‖α‖ ≤ R := by
    simpa only [α,sourceFreeNumeratorMidpointDisplacement,norm_neg] using h.midpoint (0,ψ) hψ
  obtain ⟨A,B,he,hA,hB⟩ := hbound ((0,ψ),α)
    ⟨hψ,hα,sourceFreeNumeratorMidpointDisplacement_apply hp hp1 ψ⟩
  exact ⟨A,B,fun n => by simpa only [sourceQuotientDiscSup_free_eq] using he n,hA,hB⟩

/-- Away from the removable center this is exactly the printed sine expression. -/
theorem sourceFreeSineQuotient_eq_printed (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (z : ℂ) (hz : z ≠ (Real.pi:ℂ)*n) :
    freeSineQuotient n z / sourceStandardRootOmittedJointProduct hp hp1 n (z,ψ) =
      (Complex.sin z/(z-(Real.pi:ℂ)*n)) *
        (sourceStandardRootOmittedJointProduct hp hp1 n (z,ψ))⁻¹ := by
  rw [freeSineQuotient_eq_div n z hz,div_eq_mul_inv]

end NLS.ZakharovShabat
