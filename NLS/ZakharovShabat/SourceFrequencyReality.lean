import NLS.ZakharovShabat.SourceMomentReality
import NLS.ZakharovShabat.SourceFrequencyActionExponentCompatibility
import NLS.SequenceSpaces.RealSummableApproximation

/-! # Reality of frequency maps on nonnegative actions

Hilbert realization proves reality on summable actions. Finite action
approximation and continuity give reality on the full nonnegative domain.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] [p.HolderTriple p q]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W P : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
namespace SourceAbelianMomentAtlas

/-- Any map recovering the actual frequencies is real on all nonnegative
summable actions, independently of the chosen action and target exponents. -/
theorem actionMap_im_eq_zero_on_nonnegative_summable
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (h2p : 2 ≤ p)
    (F : Coeff q → ℤ → ℂ)
    (hrec : ∀ ψ : realTypeSourceSubmodule p, ∀ n,
      F (sourceActionSequence (q := q) hp hp1 t ψ.val) n = A.renormalizedFrequency n ψ.val)
    (b : RealCoeff 1) (hb : ∀ n, 0 ≤ b n) (n : ℤ) :
    (F (Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b)) n).im = 0 := by
  obtain ⟨φ,hφ⟩ := exists_hilbertSource_of_nonnegative_actions b hb
  have hi := D.actionSequence_hilbert_realization (q := q) h2p φ b hφ
  have he := hrec (realTypeSourceExponentInclusion h2p φ) n
  rw [hi] at he
  rw [he]
  exact A.renormalizedFrequency_im_eq_zero hs _ n

/-- Continuity extends reality to every nonnegative action in the analytic
domain, without a summability assumption on that action. -/
theorem actionMap_im_eq_zero_on_nonnegative
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (h2p : 2 ≤ p)
    (F : Coeff q → Coeff r) {V : Set (Coeff q)} (hF : AnalyticOnNhd ℂ F V)
    (hrec : ∀ ψ : realTypeSourceSubmodule p, ∀ n,
      F (sourceActionSequence (q := q) hp hp1 t ψ.val) n = A.renormalizedFrequency n ψ.val)
    (b : RealCoeff q) (hb : ∀ n, 0 ≤ b n) (hbV : RealCoeff.complexCLM q b ∈ V) (n : ℤ) :
    (F (RealCoeff.complexCLM q b) n).im = 0 := by
  have hlim := (hF _ hbV).continuousAt.tendsto.comp
    (RealCoeff.tendsto_complex_finiteSummable (Coeff.doublingExponent_ne_top hp) b)
  have hcoord := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) r n).continuous.continuousAt.tendsto.comp hlim
  have him := Complex.continuous_im.continuousAt.tendsto.comp hcoord
  apply tendsto_nhds_unique him
  apply tendsto_const_nhds.congr'
  exact Filter.Eventually.of_forall (fun S =>
    (A.actionMap_im_eq_zero_on_nonnegative_summable hs D h2p (fun c n => F c n) hrec
      (RealCoeff.finiteSummable S b) (RealCoeff.finiteSummable_nonneg S b hb) n).symm)

/-- The real-part restriction is an actual real-valued analytic extension
of the frequencies on nonnegative actions, with equality in complex norm. -/
theorem exists_real_analytic_actionMap
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (h2p : 2 ≤ p)
    (F : Coeff q → Coeff r) {V : Set (Coeff q)} (hV : IsOpen V) (hF : AnalyticOnNhd ℂ F V)
    (hrec : ∀ ψ : realTypeSourceSubmodule p, ∀ n,
      F (sourceActionSequence (q := q) hp hp1 t ψ.val) n = A.renormalizedFrequency n ψ.val) :
    ∃ U : Set (RealCoeff q), IsOpen U ∧ U = RealCoeff.complexCLM q ⁻¹' V ∧
      ∃ R : RealCoeff q → RealCoeff r, AnalyticOnNhd ℝ R U ∧
        ∀ b ∈ U, (∀ n, 0 ≤ b n) → RealCoeff.complexCLM r (R b) = F (RealCoeff.complexCLM q b) := by
  let U := RealCoeff.complexCLM q ⁻¹' V
  let R := fun b : RealCoeff q => Coeff.reCLM r (F (RealCoeff.complexCLM q b))
  refine ⟨U,hV.preimage (RealCoeff.complexCLM q).continuous,rfl,R,?_,?_⟩
  · intro b hb
    exact ((Coeff.reCLM r).analyticAt _).comp
      (((hF _ hb).restrictScalars).comp ((RealCoeff.complexCLM q).analyticAt b))
  · intro b hb hpos
    exact RealCoeff.complexCLM_reCLM r _
      (A.actionMap_im_eq_zero_on_nonnegative hs D h2p F hF hrec b hpos hb)

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
