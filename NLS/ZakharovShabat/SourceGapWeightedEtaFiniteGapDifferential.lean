import NLS.ZakharovShabat.SourceGapWeightedEtaClosedDifferential
import NLS.ZakharovShabat.SourceFiniteGap

/-! # The spectral derivative formula on a finite-gap tail

Every real closed gap satisfies the explicit spectral differential
formula. In particular the formula holds outside a finite set at every
real finite-gap potential. This is the algebraic input to Lemma 16.1;
the quantitative sequence estimates remain separate.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The closed-gap spectral expression, with both the fixed-source and
moving-root terms of the terminal anti-discriminant derivative. -/
def sourceGapWeightedEtaClosedCotangent (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (sign : ℂ) (φ : CoeffPair p) : CoeffPair p →L[ℂ] ℂ :=
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n
  let dμ := fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) φ
  let dτ := fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ
  (-2 : ℂ) • (dμ - dτ + (sign*I/(2*sourceStandardRootOmittedProduct hp hp1 n φ μ)) •
    (sourceAntiDiscriminantCotangent hp hp1 μ φ + deriv (sourceAntiDiscriminantCandidate hp hp1 φ) μ • dμ))

namespace SourceAngularEtaLocalCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The closed-gap formula for the original family, with every local
annular chart supplied by the construction. -/
theorem gapWeightedEta_fderiv_closed
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ W) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0)
    (sign : ℂ) :
    fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s sign) φ.val =
      sourceGapWeightedEtaClosedCotangent hp hp1 n sign φ.val := by
  obtain ⟨a,ha,_,_,_,_,hball,_⟩ := D.psi.isolation φ
  let O := W ∩ ball φ.val a
  have hOB : O ⊆ B := fun _ h => hWB h.1
  obtain ⟨V,c,T,r,R,z₀,hφV,E⟩ :=
    D.psi.toSourcePsiIsolatingComplexExtension.exists_local_joint_angular_annulus_primitives
      O (hW.inter isOpen_ball) (fun _ h => hball h.2)
      (fun ψ hψ => D.symmetric_analytic ψ (hOB hψ))
      φ.val ⟨hφ,mem_ball_self ha⟩ φ.property n
  let ρ := (r+R)/2
  have hrρ : r < ρ := by dsimp only [ρ]; linarith [E.inner_lt_outer]
  have hρR : ρ < R := by dsimp only [ρ]; linarith [E.inner_lt_outer]
  have h := E.fderiv_gapWeightedEtaCoordinate_of_real_closed_gap ρ hrρ hρR
    ((D.roots_analytic .dirichlet n).mono (E.source_subset.trans hOB)) φ.val hφV φ.property
    (D.symmetric_analytic φ.val (hWB hφ) n).1 hgap sign
  rw [fderiv_sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet n φ.val φ.property] at h
  exact h

/-- At a real finite-gap source, the exact spectral formula holds at
all indices outside a finite set, for both signs simultaneously. -/
theorem gapWeightedEta_fderiv_finiteGap_tail
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ W)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ S : Finset ℤ, ∀ n ∉ S, ∀ sign : ℂ,
      fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s sign) φ.val =
        sourceGapWeightedEtaClosedCotangent hp hp1 n sign φ.val := by
  classical
  refine ⟨hfinite.toFinset,?_⟩
  intro n hn sign
  have hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0 := by
    by_contra h
    exact hn (hfinite.mem_toFinset.mpr h)
  exact D.gapWeightedEta_fderiv_closed W hW hWB φ hφ n hgap sign

end SourceAngularEtaLocalCommonDomainData
end NLS.ZakharovShabat
