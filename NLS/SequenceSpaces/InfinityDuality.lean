import NLS.SequenceSpaces.FullDuality
import NLS.SequenceSpaces.PairNormInfty
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Analysis.Normed.Module.HahnBanach
/-! # The full infinity dual exceeds coefficient duality

The closure of the finite sequences misses the constant-one sequence.
Hahn-Banach on the quotient therefore gives a bounded complex functional
vanishing on every finite sequence but nonzero at one. It cannot be
represented by an l1 coefficient sequence, even as the derivative of an
everywhere-analytic scalar function. The same obstruction holds in the
source's exact frequencywise sum norm on two-component infinity inputs.
-/
noncomputable section
open NLS NLS.Coeff
open scoped ENNReal
namespace NLS.Coeff

/-- The norm closure of the finitely supported coefficient sequences. -/
def finiteSupportClosure : Submodule ℂ (Coeff ⊤) := (Coeff.ofFinsupp (p := ⊤)).range.topologicalClosure

theorem one_not_mem_finiteSupportClosure : (1 : Coeff ⊤) ∉ finiteSupportClosure := by
  have hb (a : ℤ →₀ ℂ) : 1 ≤ ‖(1 : Coeff ⊤) - Coeff.ofFinsupp a‖ := by
    obtain ⟨n,hn⟩ := a.support.exists_notMem
    have h := lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞) ≠ 0)
      ((1 : Coeff ⊤)-Coeff.ofFinsupp a) n
    change ‖(1 : ℂ)-a n‖ ≤ _ at h
    simpa [Finsupp.notMem_support_iff.mp hn] using h
  have hc : IsClosed {a : Coeff ⊤ | 1 ≤ ‖1-a‖} :=
    isClosed_le continuous_const ((continuous_const.sub continuous_id).norm)
  have hs : closure (Set.range (Coeff.ofFinsupp (p := ⊤))) ⊆ {a : Coeff ⊤ | 1 ≤ ‖1-a‖} :=
    closure_minimal (by rintro _ ⟨a,rfl⟩; exact hb a) hc
  intro h
  have hz := hs h
  norm_num at hz

/-- A bounded functional invisible on all finite Fourier sums, but nonzero on one. -/
theorem exists_singular_functional : ∃ L : Coeff ⊤ →L[ℂ] ℂ,
    L 1 ≠ 0 ∧ ∀ a : ℤ →₀ ℂ, L (Coeff.ofFinsupp a) = 0 := by
  let S := finiteSupportClosure
  let : IsClosed (S : Set (Coeff ⊤)) := (Coeff.ofFinsupp (p := ⊤)).range.isClosed_topologicalClosure
  have hx : S.mkQ (1 : Coeff ⊤) ≠ 0 := by
    intro h
    exact one_not_mem_finiteSupportClosure ((Submodule.Quotient.mk_eq_zero S).mp h)
  obtain ⟨f,hf,hval⟩ := exists_dual_vector ℂ (S.mkQ (1 : Coeff ⊤)) (norm_ne_zero_iff.mpr hx)
  refine ⟨f.comp S.mkQL,?_,?_⟩
  · change f (S.mkQ 1) ≠ 0
    rw [hval]
    exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  · intro a
    have ha : Coeff.ofFinsupp (p := ⊤) a ∈ S :=
      (Coeff.ofFinsupp (p := ⊤)).range.le_topologicalClosure ⟨a,rfl⟩
    change f (S.mkQ (Coeff.ofFinsupp a)) = 0
    rw [show S.mkQ (Coeff.ofFinsupp a) = 0 from (Submodule.Quotient.mk_eq_zero S).mpr ha,map_zero]

/-- The l1 pairing is not onto the full continuous dual of linfinity. -/
theorem exists_nonrepresented_functional : ∃ L : Coeff ⊤ →L[ℂ] ℂ,
    ∀ a : Coeff 1, Coeff.dualPairing a ≠ L := by
  obtain ⟨L,hL,hfin⟩ := exists_singular_functional
  refine ⟨L,?_⟩
  intro a ha
  have hz (n : ℤ) : L (lp.single ⊤ n 1) = 0 := by
    have he : Coeff.ofFinsupp (p := ⊤) (Finsupp.single n 1) = lp.single ⊤ n 1 := by
      ext k
      simp [Coeff.ofFinsupp_apply,lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
    rw [← he]
    exact hfin _
  have ha0 : a = 0 := by
    ext n
    have he := congrArg (fun K : Coeff ⊤ →L[ℂ] ℂ => K (lp.single ⊤ n 1)) ha
    change a n = 0
    simpa only [Coeff.dualPairing_single,hz] using he
  apply hL
  rw [← ha,ha0]
  simp

/-- Analyticity alone does not supply a coefficient gradient at an infinity source exponent. -/
theorem exists_analytic_without_coefficient_gradient :
    ∃ F : Coeff ⊤ → ℂ, AnalyticOnNhd ℂ F Set.univ ∧
      ∀ x, ¬∃ a : Coeff 1, Coeff.dualPairing a = fderiv ℂ F x := by
  obtain ⟨L,hL⟩ := exists_nonrepresented_functional
  refine ⟨L,fun x _ => L.analyticAt x,?_⟩
  intro x ⟨a,ha⟩
  exact hL a (ha.trans L.hasFDerivAt.fderiv)


/-- The original frequencywise sum norm at infinity also has analytic functionals
without a conjugate coefficient-pair gradient. -/
theorem exists_source_pair_without_gradient :
    ∃ F : CoeffPairInfty → ℂ, AnalyticOnNhd ℂ F Set.univ ∧
      ∀ x, ¬∃ g : CoeffPair 1, ∀ h : CoeffPairInfty,
        fderiv ℂ F x h =
          Coeff.dualPairing (Coeff.reflection g.fst) (CoeffPairInfty.fst h) +
          Coeff.dualPairing (Coeff.reflection g.snd) (CoeffPairInfty.snd h) := by
  obtain ⟨L,hL⟩ := exists_nonrepresented_functional
  let K : CoeffPairInfty →L[ℂ] ℂ :=
    L.comp ((ContinuousLinearMap.fst ℂ (Coeff ⊤) (Coeff ⊤)).comp
      CoeffPairInfty.toMax.toContinuousLinearMap)
  refine ⟨K,fun x _ => K.analyticAt x,?_⟩
  intro x ⟨g,hg⟩
  apply hL (Coeff.reflection g.fst)
  ext a
  have he := hg (CoeffPairInfty.ofPair a 0)
  rw [K.hasFDerivAt.fderiv] at he
  change L a = Coeff.dualPairing (Coeff.reflection g.fst) a +
    Coeff.dualPairing (Coeff.reflection g.snd) (0 : Coeff ⊤) at he
  simpa only [map_zero,add_zero] using he.symm

/-- Exact source-exponent scope of full coefficient-dual representation. -/
theorem dualPairing_surjective_iff {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [q.HolderConjugate p] :
    Function.Surjective (dualPairing (p := q) (q := p)) ↔ p ≠ ⊤ := by
  constructor
  · intro h hp
    subst p
    have hq : q = 1 := ENNReal.HolderConjugate.unique ⊤ q 1
    subst q
    obtain ⟨L,hL⟩ := exists_nonrepresented_functional
    obtain ⟨a,ha⟩ := h L
    exact hL a ha
  · intro hp L
    exact ⟨fullCotangent hp L,dualPairing_fullCotangent hp L⟩

end NLS.Coeff
