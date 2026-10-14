import NLS.ZakharovShabat.ResonantDiagonalQuadratic
import NLS.ZakharovShabat.ResonantDeterminantBounds
import NLS.SequenceSpaces.QuasiExponentEmbedding
import NLS.Fourier.FreeLatticeSampledRows
import NLS.SequenceSpaces.PeriodDoubling
import NLS.SequenceSpaces.UniformSelectionSup
import NLS.SequenceSpaces.CoordinateNormSup
import NLS.SequenceSpaces.RefinedOnePlusDecomposition

/-!
# Half-exponent disk suprema of the quadratic diagonal

Independent spectral samples are lifted to even Hilbert rows. Uniform
sampling controls the literal supremum on every free quarter-π disk in
each finite exponent r>1 with r≥p/2. On bounded input families there is
one fixed l(p/2)+l(1+) decomposition, including p/2≤1.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]
local instance resonantDiagonalQuadraticSummabilityConjFact : Fact (1 ≤ p.conjExponent) :=
  ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- Lift independent spectral samples to even lattice indices; fill odd rows freely. -/
def resonantDiagonalQuadraticSample (z : ℤ → ℂ) (j : ℤ) : ℂ :=
  if j%2 = 0 then z (j/2)+(Real.pi:ℂ)*(j/2) else (Real.pi:ℂ)*j

@[simp] theorem resonantDiagonalQuadraticSample_even (z : ℤ → ℂ) (n : ℤ) :
    resonantDiagonalQuadraticSample z (2*n) = z n+(Real.pi:ℂ)*n := by simp [resonantDiagonalQuadraticSample]

/-- The lifted samples remain within quarter-π of their own lattice centers. -/
theorem norm_resonantDiagonalQuadraticSample_sub_free_le (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, ‖z n-(Real.pi:ℂ)*n‖ ≤ Real.pi/4) (j : ℤ) :
    ‖resonantDiagonalQuadraticSample z j-(Real.pi:ℂ)*j‖ ≤ Real.pi/4 := by
  by_cases hj : j%2 = 0
  · have he : j = 2*(j/2) := by omega
    rw [he,resonantDiagonalQuadraticSample_even]
    convert hz (j/2) using 1
    congr 1
    push_cast
    ring
  · simp only [resonantDiagonalQuadraticSample,if_neg hj,sub_self,norm_zero]
    positivity

/-- Every independent selection has the same half-exponent Hilbert bound. -/
theorem exists_resonantDiagonalQuadratic_samples (hp : p ≠ ⊤) (hr1 : 1 < r) (hr : r ≠ ⊤) (hpr : p/2 ≤ r)
    (a b : Coeff p) (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, ‖z n-(Real.pi:ℂ)*n‖ ≤ Real.pi/4) :
    ∃ d : Coeff r, (∀ n : ℤ, d n = resonantDiagonalQuadratic a b n (z n)) ∧
      ‖d‖ ≤ Real.pi⁻¹*(Fourier.hilbertTransformBound hr1 hr+‖Fourier.hilbertSquareCoeffs‖)*(‖a‖*‖b‖) := by
  let f := resonantDiagonalPairProduct a b
  let fR : Coeff r := ⟨fun j => f j,(lp.memℓp f).of_exponent_ge hpr⟩
  have hpos : 0 < p/2 := ENNReal.div_pos (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) (by norm_num)
  have hnorm : ‖fR‖ ≤ ‖a‖*‖b‖ :=
    (Coeff.norm_quasiExponentInclusion_le hpos (zero_lt_one.trans hr1) hr hpr f).trans (norm_resonantDiagonalPairProduct_le hp a b)
  let Z := resonantDiagonalQuadraticSample z
  have hZ : ∀ j ∈ (univ : Set ℤ), ‖Z j-(Real.pi:ℂ)*j‖ ≤ Real.pi/4 := fun j _ => norm_resonantDiagonalQuadraticSample_sub_free_le z hz j
  let d : Coeff r := -Coeff.periodHalve (Fourier.freeLatticeRows hr1 hr univ Z hZ fR)
  refine ⟨d,?_,?_⟩
  · intro n
    change -Fourier.freeLatticeRows hr1 hr univ Z hZ fR (2*n) = _
    rw [Fourier.freeLatticeRows_apply hr1 hr univ Z hZ fR (mem_univ _),← tsum_neg]
    apply tsum_congr
    intro j
    by_cases hj : j = 2*n
    · simp [hj]
    · simp only [if_neg hj,Z,resonantDiagonalQuadraticSample_even]
      change -(b j*a (-j)/((Real.pi:ℂ)*j-(z n+(Real.pi:ℂ)*n))) =
        b j*a (-j)/(z n+(Real.pi:ℂ)*n-(Real.pi:ℂ)*j)
      rw [← div_neg]
      congr 1
      ring
  · have hC : 0 ≤ Real.pi⁻¹*(Fourier.hilbertTransformBound hr1 hr+‖Fourier.hilbertSquareCoeffs‖) := by
      have := Fourier.hilbertTransformBound_nonneg hr1 hr
      positivity
    calc
      ‖d‖ = ‖Coeff.periodHalve (Fourier.freeLatticeRows hr1 hr univ Z hZ fR)‖ := norm_neg _
      _ ≤ ‖Fourier.freeLatticeRows hr1 hr univ Z hZ fR‖ := Coeff.norm_periodHalve_le _
      _ ≤ Real.pi⁻¹*(Fourier.hilbertTransformBound hr1 hr+‖Fourier.hilbertSquareCoeffs‖)*‖fR‖ :=
        Fourier.norm_freeLatticeRows_le hr1 hr univ Z hZ fR
      _ ≤ _ := mul_le_mul_of_nonneg_left hnorm hC

/-- The literal norm supremum on the full free quarter-π disk. -/
def resonantDiagonalQuadraticSup (a b : Coeff p) (n : ℤ) : ℝ :=
  sSup ((fun z => ‖resonantDiagonalQuadratic a b n z‖) '' refinedResonantDisk n)

/-- The supremum sequence has a quadratic norm bound at each admissible exponent. -/
theorem exists_resonantDiagonalQuadraticSup (hp : p ≠ ⊤) (hr1 : 1 < r) (hr : r ≠ ⊤) (hpr : p/2 ≤ r)
    (a b : Coeff p) :
    ∃ d : Coeff r, (∀ n : ℤ, d n = (resonantDiagonalQuadraticSup a b n : ℂ)) ∧
      (∀ n : ℤ, ∀ z ∈ refinedResonantDisk n, ‖resonantDiagonalQuadratic a b n z‖ ≤ ‖d n‖) ∧
      ‖d‖ ≤ Real.pi⁻¹*(Fourier.hilbertTransformBound hr1 hr+‖Fourier.hilbertSquareCoeffs‖)*(‖a‖*‖b‖) := by
  let K := Real.pi⁻¹*(Fourier.hilbertTransformBound hr1 hr+‖Fourier.hilbertSquareCoeffs‖)*(‖a‖*‖b‖)
  have hK : 0 ≤ K := by
    have := Fourier.hilbertTransformBound_nonneg hr1 hr
    dsimp [K]
    positivity
  have hD (n : ℤ) : (refinedResonantDisk n).Nonempty :=
    ⟨(Real.pi:ℂ)*n,mem_ball_self (by positivity)⟩
  have hsel (z : ℤ → ℂ) (hz : ∀ n, z n ∈ refinedResonantDisk n) :
      ∃ d : Coeff r, (∀ n ∈ (univ : Set ℤ), d n = resonantDiagonalQuadratic a b n (z n)) ∧ ‖d‖ ≤ K := by
    obtain ⟨d,hd,hn⟩ := exists_resonantDiagonalQuadratic_samples hp hr1 hr hpr a b z
      (fun n => (show ‖z n-(Real.pi:ℂ)*n‖ < Real.pi/4 by
        simpa only [refinedResonantDisk,mem_ball,dist_eq_norm] using hz n).le)
    exact ⟨d,fun n _ => hd n,hn⟩
  obtain ⟨B,hB,_,_,hBn⟩ := exists_uniformSelectionSup hr univ refinedResonantDisk hD
    (resonantDiagonalQuadratic a b) K hK hsel
  obtain ⟨d,hd,hmajor,hn⟩ := exists_coordinateNormSup (ne_of_gt (zero_lt_one.trans hr1))
    refinedResonantDisk hD (resonantDiagonalQuadratic a b) B (fun n => hB n (mem_univ _))
  exact ⟨d,hd,hmajor,hn.trans hBn⟩

/-- One pair of summands serves every finite projection of the l(1+) component. -/
theorem exists_uniform_resonantDiagonalQuadraticSup_decomposition (hp : p ≠ ⊤) (M : ℝ) (hM : 0 ≤ M) :
    ∃ A : (Coeff p × Coeff p) → Coeff (p/2), ∃ B : (Coeff p × Coeff p) → CoeffOnePlus,
      (∀ x : Coeff p × Coeff p, ‖x.1‖ ≤ M → ‖x.2‖ ≤ M → ∀ n : ℤ,
        (resonantDiagonalQuadraticSup x.1 x.2 n : ℂ) = A x n+(B x).1 n) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ x : Coeff p × Coeff p, ‖x.1‖ ≤ M → ‖x.2‖ ≤ M → ‖A x‖ ≤ C) ∧
      ∀ (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤),
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Coeff p × Coeff p, ‖x.1‖ ≤ M → ‖x.2‖ ≤ M →
          ‖CoeffOnePlus.toCoeff q hq1 hq (B x)‖ ≤ C := by
  let S : Set (Coeff p × Coeff p) := {x | ‖x.1‖ ≤ M ∧ ‖x.2‖ ≤ M}
  have hhalf : p/2 ≠ ⊤ := ENNReal.div_ne_top hp (by norm_num)
  have hb (q : ℝ≥0∞) (hq : q ≠ ⊤) (hq1 : 1 < q) (hpq : p/2 ≤ q) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∃ d : Coeff q,
        (∀ n, d n = (resonantDiagonalQuadraticSup x.1 x.2 n : ℂ)) ∧ ‖d‖ ≤ C := by
    let : Fact (1 ≤ q) := ⟨hq1.le⟩
    let K := Real.pi⁻¹*(Fourier.hilbertTransformBound hq1 hq+‖Fourier.hilbertSquareCoeffs‖)
    have hK : 0 ≤ K := by
      have := Fourier.hilbertTransformBound_nonneg hq1 hq
      dsimp [K]
      positivity
    refine ⟨K*(M*M),mul_nonneg hK (mul_nonneg hM hM),?_⟩
    intro x hx
    obtain ⟨d,hd,_,hn⟩ := exists_resonantDiagonalQuadraticSup hp hq1 hq hpq x.1 x.2
    exact ⟨d,hd,hn.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul hx.1 hx.2 (norm_nonneg _) hM) hK)⟩
  obtain ⟨A,B,he,hA,hB⟩ := Coeff.exists_onePlus_decomposition_of_refined S
    (fun x n => (resonantDiagonalQuadraticSup x.1 x.2 n : ℂ)) hhalf hb
  refine ⟨A,B,fun x ha hb => he x ⟨ha,hb⟩,?_,?_⟩
  · obtain ⟨C,hC,hbound⟩ := hA
    exact ⟨C,hC,fun x ha hb => hbound x ⟨ha,hb⟩⟩
  · intro q hq1 hq
    obtain ⟨C,hC,hbound⟩ := hB q hq1 hq
    exact ⟨C,hC,fun x ha hb => hbound x ⟨ha,hb⟩⟩

end NLS.ZakharovShabat
