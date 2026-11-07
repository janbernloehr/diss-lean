import NLS.KdV.HminusOneDirichletComplexLabels
import NLS.KdV.HminusOneDirichletLabelAsymptotics

/-! The full complex construction preserves the ENTIRE real Dirichlet
sequence at the same positive index and the exact free normalization. -/
noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped Classical
namespace NLS.KdV

/-- Complex global labels restrict to the previously verified full real
labels, with no change of central indexing or potential distribution. -/
theorem hillHminusDirichletComplexLabels_eq_real (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    hillHminusDirichletComplexLabels q n = (hillHminusDirichletLabels q hq n:ℂ) := by
  let nu : ℕ → ℂ := fun j => (hillHminusDirichletLabels q hq (Equiv.pnatEquivNat.symm j):ℂ)
  have hinj : Function.Injective nu := by
    intro i j he
    exact Equiv.pnatEquivNat.symm.injective
      ((strictMono_hillHminusDirichletLabels q hq).injective (Complex.ofReal_inj.mp he))
  have hf (e : ℂ) : {j | nu j = e}.Finite :=
    (Set.finite_singleton e).preimage hinj.injOn
  have ho : Monotone (fun j => complexLexKey (nu j)) := by
    intro i j hij
    change complexLexLE (hillHminusDirichletLabels q hq (Equiv.pnatEquivNat.symm i):ℂ)
      (hillHminusDirichletLabels q hq (Equiv.pnatEquivNat.symm j):ℂ)
    apply (complexLexLE_ofReal_iff _ _).mpr
    exact (strictMono_hillHminusDirichletLabels q hq).monotone
      (OrderIso.pnatIsoNat.symm.monotone hij)
  have hm (e : ℂ) : (∑ᶠ j : ℕ, if nu j = e then (1:ℕ) else 0) =
      singularDirichletAlgebraicMultiplicity (periodOneOriginal q) e := by
    calc
      _ = ∑ᶠ k : ℕ+, if (hillHminusDirichletLabels q hq k:ℂ) = e then (1:ℕ) else 0 :=
        finsum_comp_equiv Equiv.pnatEquivNat.symm
      _ = analyticOrderNatAt (hillHminusDirichlet q) e :=
        hillHminusDirichletLabels_global_multiplicity q hq e
      _ = _ := (singularDirichletAlgebraicMultiplicity_eq_analyticOrderNatAt q e).symm
  obtain ⟨u,c,N,h⟩ := hillHminusDirichletComplexSequence_spec q
  have he := NLS.ordered_complex_nat_enumeration_unique
    (hillHminusDirichletComplexSequence q) nu h.finite_fiber hf h.ordered ho
      (fun e => (h.multiplicity e).trans (hm e).symm)
  simpa only [hillHminusDirichletComplexLabels,nu,Equiv.symm_apply_apply]
    using congrFun he (Equiv.pnatEquivNat n)

/-- The complete complex free sequence is EXACTLY n^2*pi^2, starting at one. -/
theorem hillHminusDirichletComplexLabels_zero (n : ℕ+) :
    hillHminusDirichletComplexLabels 0 n = ((Real.pi:ℂ)*(n:ℕ))^2 := by
  have hq : IsRealPeriodOneHminusOne (0:PeriodOneHminusOne) := by intro k; simp
  rw [hillHminusDirichletComplexLabels_eq_real 0 hq,hillHminusDirichletLabels_zero hq n]
  simp only [Complex.ofReal_pow,Complex.ofReal_mul,Complex.ofReal_natCast]

end NLS.KdV
