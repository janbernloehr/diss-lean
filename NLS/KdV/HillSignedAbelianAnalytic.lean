import NLS.KdV.HillSignedAbelianHamiltonianVariation
import NLS.ComplexAnalysis.ConjugateAnalytic

/-! # Negative physical Abelian coordinates analytic through closed gaps

Conjugating the positive coordinate extension in source and target gives
an actual complex Banach power series for the negative coordinate. The
matching neighborhood is in the genuine real period-one potential space.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- The actual negative physical coordinate has a complex analytic matching
extension at every real source, including a closed selected gap. -/
theorem exists_hillNegativeAbelianCoordinate_analytic_extension (n : ℕ) (hn : 1≤n) :
    ∃ H : Coeff 2 → ℂ, AnalyticAt ℂ H (SpectralWeight.one.toCoeff q) ∧
      H (SpectralWeight.one.toCoeff q)=conj (hillDirichletAbelianCoordinate q hq hr n hn) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        H (SpectralWeight.one.toCoeff p.val)=conj (hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn) := by
  obtain ⟨Z,hZ,_hZ0,_hclosed,hZmatch⟩ :=
    exists_hillDirichletAbelianCoordinate_analytic_extension q hq hr h0q h0r n hn
  let H : Coeff 2 → ℂ := fun p => conj (Z (star (Coeff.reflection p)))
  have hreal (p : RealPeriodOneHillPotential) :
      star (SpectralWeight.one.toCoeff p.val)=Coeff.reflection (SpectralWeight.one.toCoeff p.val) := by
    ext k
    change conj ((SpectralWeight.one.toCoeff p.val) k)=(SpectralWeight.one.toCoeff p.val) (-k)
    exact (p.property.2 k).symm
  have hs := analyticAt_star_star hZ
  rw [hreal (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)] at hs
  have hR : AnalyticAt ℂ (fun p : Coeff 2 => Coeff.reflection p) (SpectralWeight.one.toCoeff q) :=
    Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _
  have hH : AnalyticAt ℂ H (SpectralWeight.one.toCoeff q) := by
    simpa only [H,Function.comp_def,Complex.star_def] using hs.comp hR
  have hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      H (SpectralWeight.one.toCoeff p.val)=conj (hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn) := by
    filter_upwards [hZmatch] with p hp
    have he : star (Coeff.reflection (SpectralWeight.one.toCoeff p.val))=SpectralWeight.one.toCoeff p.val := by
      ext k
      change conj ((SpectralWeight.one.toCoeff p.val) (-k))=(SpectralWeight.one.toCoeff p.val) k
      rw [p.property.2 k,conj_conj]
    dsimp only [H]
    rw [he,hp]
  exact ⟨H,hH,hmatch.self_of_nhds,hmatch⟩

end NLS.KdV
