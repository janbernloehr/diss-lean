import NLS.ZakharovShabat.SourceLemma4_5
import NLS.ZakharovShabat.SourceLemma4_3Physical
import NLS.SequenceSpaces.PairExponentEmbedding
import NLS.Fourier.PeriodOneCoefficients

/-!
# Lemma 4.5 at the printed p=1 endpoint

An absolutely summable period-one coefficient pair synthesizes a continuous
physical potential. Its bounded coefficient-preserving inclusion into p=2
has exactly that potential's unit-interval Fourier coefficients. The completed
Hilbert reflection therefore realizes the same classical boundary spectrum.
Pulling the original Hilbert trace branches back along this bounded inclusion
proves their analyticity in the original p=1 norm. No bounded reflection into
the period-two p=1 space is asserted or needed. Multiplicity here is that of
the original Hilbert boundary realization, whose eigenvalue set is proved to
be the classical physical interval eigenvalue set.
-/

noncomputable section
open scoped ENNReal
open NLS.Fourier MeasureTheory Set
namespace NLS.ZakharovShabat

/-- The continuous physical interval potential of an original p=1 coefficient pair. -/
def sourceOnePhysicalPotential (φ : CoeffPair 1) (x : ℝ) : ℂ × ℂ :=
  (periodOneSynthesis φ.fst x, periodOneSynthesis φ.snd x)

theorem continuous_sourceOnePhysicalPotential (φ : CoeffPair 1) : Continuous (sourceOnePhysicalPotential φ) :=
  (continuous_periodOneSynthesis φ.fst).prodMk (continuous_periodOneSynthesis φ.snd)

theorem memLp_sourceOnePhysicalPotential (φ : CoeffPair 1) :
    MemLp (sourceOnePhysicalPotential φ) 2 (volume.restrict (Ioc 0 1)) :=
  memLp_prod_iff.mpr ⟨memLp_two_interval (continuous_periodOneSynthesis φ.fst) 0 1 (by norm_num),
    memLp_two_interval (continuous_periodOneSynthesis φ.snd) 0 1 (by norm_num)⟩

/-- Bounded coefficient-preserving inclusion from the original p=1 norm into p=2. -/
def sourceOneToHilbert : CoeffPair 1 →L[ℂ] CoeffPair 2 := CoeffPair.exponentInclusion (by norm_num)

/-- The included coefficients are exactly those of the same continuous physical potential. -/
theorem sourceOneToHilbert_coefficients (φ : CoeffPair 1) :
    sourceUnitIntervalL2Coefficients (sourceOnePhysicalPotential φ) (memLp_sourceOnePhysicalPotential φ) =
      sourceOneToHilbert φ := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> apply lp.ext <;> funext n
  · change unitIntervalMemLpCoefficients (fun x => periodOneSynthesis φ.fst x) _ n = φ.fst n
    exact (unitIntervalMemLpCoefficients_apply _ _ n).trans
      ((intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num) _ n).trans
        (periodOneCoefficient_synthesis φ.fst n))
  · change unitIntervalMemLpCoefficients (fun x => periodOneSynthesis φ.snd x) _ n = φ.snd n
    exact (unitIntervalMemLpCoefficients_apply _ _ n).trans
      ((intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num) _ n).trans
        (periodOneCoefficient_synthesis φ.snd n))

/-- The reflected Hilbert potential is the actual physical Dirichlet reflection. -/
theorem sourceOneToHilbert_reflected (φ : CoeffPair 1) :
    CoeffPair.toMax 2 (sourceReflectedPotential (by norm_num) (by simp) (sourceOneToHilbert φ)) =
      BoundaryCondition.dirichletPotentialCoefficients (sourceOnePhysicalPotential φ) (memLp_sourceOnePhysicalPotential φ) := by
  have he := sourceIntervalExtensionL2_ofFunction .dirichlet (sourceOnePhysicalPotential φ) (memLp_sourceOnePhysicalPotential φ)
  rw [sourceOneToHilbert_coefficients] at he
  exact congrArg (CoeffPair.toMax 2) he

/-- The original Hilbert boundary trace branch pulled back to the p=1 input space. -/
def sourceOneBoundaryEigenvalue (b : BoundaryCondition) (φ : CoeffPair 1) (n : ℤ) : ℂ :=
  sourceBoundaryEigenvalue b (by norm_num) (by simp) (sourceOneToHilbert φ) n

/-- The Hilbert realization of the ordinary boundary spectrum for p=1 input. -/
def sourceOneBoundarySpectrum (b : BoundaryCondition) (φ : CoeffPair 1) : Set ℂ :=
  sourceBoundarySpectrum b (by simp)
    (sourceReflectedPotential (by norm_num) (by simp) (sourceOneToHilbert φ))
    (sourceReflectedPotential_mem (by norm_num) (by simp) (sourceOneToHilbert φ))

/-- The endpoint realization has exactly the classical interval eigenvalues. -/
theorem sourceOneBoundarySpectrum_eq_classical (b : BoundaryCondition) (φ : CoeffPair 1) :
    sourceOneBoundarySpectrum b φ = BoundaryCondition.classicalEigenvalues b (sourceOnePhysicalPotential φ) := by
  rw [sourceOneBoundarySpectrum,sourceBoundarySpectrum_eq,
    BoundaryCondition.classicalEigenvalues_eq_boundarySpectrum b _ (memLp_sourceOnePhysicalPotential φ)]
  congr 1
  exact sourceOneToHilbert_reflected φ

/-- Algebraic multiplicity in the original Hilbert boundary realization. -/
def sourceOneBoundaryMultiplicity (b : BoundaryCondition) (φ : CoeffPair 1) (z : ℂ) : ℕ :=
  sourceBoundaryAlgebraicMultiplicity b (by simp)
    (sourceReflectedPotential (by norm_num) (by simp) (sourceOneToHilbert φ))
    (sourceReflectedPotential_mem (by norm_num) (by simp) (sourceOneToHilbert φ)) z

/-- The printed endpoint: original p=1 analytic branches with the actual classical eigenvalue sets. -/
theorem sourceLemma4_5_one (φ : CoeffPair 1) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair 1), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ IsConnected U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ b : BoundaryCondition, ∀ n : ℤ, N₀ < n.natAbs →
        AnalyticOnNhd ℂ (fun ψ => sourceOneBoundaryEigenvalue b ψ n) U ∧
        ∀ ψ ∈ U,
          BoundaryCondition.classicalEigenvalues b (sourceOnePhysicalPotential ψ) ∩
            Metric.ball ((Real.pi : ℂ)*n) (Real.pi/4) = {sourceOneBoundaryEigenvalue b ψ n} ∧
          sourceOneBoundaryMultiplicity b ψ (sourceOneBoundaryEigenvalue b ψ n) = 1 := by
  obtain ⟨N,V,hN,ho,hconv,_,hφ,h0,h⟩ := sourceLemma4_5 (by norm_num) (by simp) (sourceOneToHilbert φ)
  let U : Set (CoeffPair 1) := sourceOneToHilbert ⁻¹' V
  have hUc : Convex ℝ U := hconv.linear_preimage (sourceOneToHilbert.restrictScalars ℝ).toLinearMap
  have hU0 : (0 : CoeffPair 1) ∈ U := by simpa [U] using h0
  refine ⟨N,U,hN,ho.preimage sourceOneToHilbert.continuous,hUc,⟨⟨0,hU0⟩,hUc.isPreconnected⟩,hφ,hU0,?_⟩
  intro b n hn
  refine ⟨?_,?_⟩
  · intro ψ hψ
    exact ((h b n hn).1 (sourceOneToHilbert ψ) hψ).comp (sourceOneToHilbert.analyticAt ψ)
  · intro ψ hψ
    obtain ⟨hs,hm⟩ := (h b n hn).2 (sourceOneToHilbert ψ) hψ
    refine ⟨?_,hm⟩
    ext z
    rw [← sourceOneBoundarySpectrum_eq_classical,sourceOneBoundarySpectrum]
    change (z ∈ sourceBoundarySpectrum b _ _ _ ∧ z ∈ Metric.ball _ _) ↔ _
    rw [← mem_sourceBoundaryEnclosedSpectrum,hs]
    simp only [Finset.mem_singleton,Set.mem_singleton_iff,sourceOneBoundaryEigenvalue]

end NLS.ZakharovShabat

