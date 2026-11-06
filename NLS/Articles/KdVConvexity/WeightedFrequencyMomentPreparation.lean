import NLS.KdV.HillHminusWeightedSecondMoments
import NLS.SequenceSpaces.SignedWeightedMomentPairs

/-! # Actual analytic positive-gap moment sums in the rough source topology

The full signed normalized differential branch and literal moments are
retained. The next work must identify the shifted Miura pullback with the
physical Hill frequency formula, prove chart independence and descend to
the original weighted action domain. No physical frequency equality is
asserted by the present preparation theorem.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.Articles.KdVConvexity
open NLS.KdV NLS.ZakharovShabat

def positiveWeightedMomentSum {W : Set (CoeffPair 2)}
    {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s)
    (n : ℕ+) (ψ : CoeffPair 2) : ℂ :=
  ∑' k : ℕ+, (k : ℂ)*(A.moment (n : ℤ) (k : ℤ) 2 ψ-A.moment (n : ℤ) (-(k : ℤ)) 2 ψ)

/-- At every actual real Hminus1 source, ONE complex-open source
neighborhood supports all positive-index signed-pair moment sums,
absolutely and analytically, with one linear-index bound. No atlas,
Miura inverse, normalized numerator, period or series bound is input. -/
theorem exists_analytic_positive_weighted_moment_source_chart
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (M : ℝ) :
    ∃ P : HillHminusPsiChart, ∃ c : ℝ, ∃ W : Set (CoeffPair 2),
      ∃ A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W P.family.roots,
      ∃ T : Set PeriodOneHminusOne, 0<c ∧ M<c ∧ P.miura.energyShift=(c : ℂ)^2 ∧
        IsOpen T ∧ q ∈ T ∧ T ⊆ P.source ∧
        (∀ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val ∈ T →
          ∀ n : ℕ+, ∀ E : ℂ, P.numerator n (E,hillOriginalHminusSource p.val)=
            hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n n.pos E) ∧
        (∀ n : ℕ+, AnalyticOnNhd ℂ
          (fun a => positiveWeightedMomentSum A n (hillMiuraDiagonal (P.miura.lift a))) T) ∧
        (∀ a ∈ T, ∀ n : ℕ+, Summable (fun k : ℕ+ =>
          ‖(k : ℂ)*(A.moment (n : ℤ) (k : ℤ) 2 (hillMiuraDiagonal (P.miura.lift a))-
            A.moment (n : ℤ) (-(k : ℤ)) 2 (hillMiuraDiagonal (P.miura.lift a)))‖)) ∧
        (∀ a ∈ T, ∀ n : ℕ+, positiveWeightedMomentSum A n (hillMiuraDiagonal (P.miura.lift a))=
          A.weightedSecondMomentSum (n : ℤ) (hillMiuraDiagonal (P.miura.lift a))) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ T, ∀ n : ℕ+,
          ‖positiveWeightedMomentSum A n (hillMiuraDiagonal (P.miura.lift a))‖ ≤ (1+(n : ℝ))*C := by
  obtain ⟨P,c,W,A,T,hc,hMc,hshift,hT,hqT,hTP,hreal,houtside,ha,hsum,C,hC,hbound⟩ :=
    exists_hillHminus_weighted_secondMoment_chart q hq M
  have hp (a : PeriodOneHminusOne) (haT : a ∈ T) (n : ℕ+) :=
    NLS.SequenceSpaces.int_weighted_sum_eq_positive_pairs
      (fun k : ℤ => A.moment (n : ℤ) k 2 (hillMiuraDiagonal (P.miura.lift a)))
      (hsum a haT (n : ℤ))
  have he (a : PeriodOneHminusOne) (haT : a ∈ T) (n : ℕ+) :
      positiveWeightedMomentSum A n (hillMiuraDiagonal (P.miura.lift a))=
        A.weightedSecondMomentSum (n : ℤ) (hillMiuraDiagonal (P.miura.lift a)) := (hp a haT n).2.symm
  refine ⟨P,c,W,A,T,hc,hMc,hshift,hT,hqT,hTP,?_,?_,fun a haT n => (hp a haT n).1,he,C,hC,?_⟩
  · intro p hpT n E
    exact congrFun (P.numerator_eq_original p (hTP hpT) hreal
      (houtside _ (hTP hpT).1) c hshift n) E
  · intro n a haT
    exact (ha (n : ℤ) a haT).congr
      (Filter.eventuallyEq_of_mem (hT.mem_nhds haT) (fun b hb => (he b hb n).symm))
  · intro a haT n
    rw [he a haT n]
    simpa only [Int.cast_natCast,norm_natCast,Complex.norm_natCast] using hbound a haT (n : ℤ)

end NLS.Articles.KdVConvexity
