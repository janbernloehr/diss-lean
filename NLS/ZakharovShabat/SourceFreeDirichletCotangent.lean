import NLS.ZakharovShabat.SourceFreeSpectralDifferentials
import NLS.ZakharovShabat.SourceBoundaryExponentDifferential

/-! # The exact free Dirichlet functional at finite source exponents

The Hilbert identity extends by exponent compatibility and density of
finite Fourier sources. Its first component reads frequency -n and its
second component reads n, both with coefficient one half.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The exact free half-wave functional in the source coefficient convention. -/
def sourceFreeDirichletCotangent (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) : CoeffPair p →L[ℂ] ℂ :=
  (1/2 : ℂ) •
    (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p (-n)).comp
      ((ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)).comp (CoeffPair.toMax p).toContinuousLinearMap))+
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp
      ((ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)).comp (CoeffPair.toMax p).toContinuousLinearMap)))

@[simp] theorem sourceFreeDirichletCotangent_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) (h : CoeffPair p) :
    sourceFreeDirichletCotangent p n h = (1/2 : ℂ)*(h.fst (-n)+h.snd n) := rfl

/-- The genuine zero-source root derivative is the exact free functional
for every finite source exponent at least two. -/
theorem fderiv_canonicalDirichletRoot_zero_eq_free
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) (n : ℤ) :
    fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) 0 =
      sourceFreeDirichletCotangent p n := by
  let L := fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) 0
  have hfinite (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
      L (CoeffPair.ofFinsupp a) = sourceFreeDirichletCotangent p n (CoeffPair.ofFinsupp a) := by
    have he := congrArg (fun T : CoeffPair 2 →L[ℂ] ℂ => T (CoeffPair.ofFinsupp a))
      (fderiv_canonicalPeriodOneBoundaryRoots_exponent (by simp) hp (by norm_num) hp1 h2p
        .dirichlet n ⟨0,by intro k; simp⟩)
    simp only [ContinuousLinearMap.comp_apply,map_zero] at he
    calc
      _ = L (CoeffPair.exponentInclusion h2p (CoeffPair.ofFinsupp (p := 2) a)) := by
        rw [CoeffPair.exponentInclusion_ofFinsupp]
      _ = (fderiv ℂ (fun ψ : CoeffPair 2 => canonicalPeriodOneBoundaryRoots
          (by simp) (by norm_num) .dirichlet ψ n) 0) (CoeffPair.ofFinsupp a) := he.symm
      _ = _ := by
        rw [fderiv_canonicalPeriodOneBoundaryRoot_zero,sourceFreeDirichletCotangent_apply]
        rfl
  have heq := CoeffPair.eq_of_continuous_of_finsupp hp L (sourceFreeDirichletCotangent p n)
    L.continuous (sourceFreeDirichletCotangent p n).continuous hfinite
  ext h
  exact congrFun heq h

end NLS.ZakharovShabat
