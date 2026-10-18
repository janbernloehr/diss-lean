import NLS.ZakharovShabat.SourceBirkhoffSpectralTerminal
import NLS.ZakharovShabat.SourceBirkhoffFourier

/-! # Exact reduction of the remaining Fourier error

The actual rectangular Fourier remainder splits into the proved
normalization and angular error plus two literal spectral errors.
Their h2 membership is an explicit hypothesis of the reduction below;
this module does not establish their decay, full one-smoothing, or
analyticity into the stronger target.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal

namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The precise remaining midpoint/Dirichlet error in the original Fourier convention. -/
def sourceEtaMidpointFourierError (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) : ℂ :=
  sourceDirichletMidpointDisplacement hp hp1 ψ n-(ψ.fst (-n)+ψ.snd n)/2

/-- The precise remaining terminal sine error in the original Fourier convention. -/
def sourceEtaSineFourierError (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) : ℂ :=
  sourceDirichletEtaSineNumerator hp hp1 n ψ-(I/2)*(ψ.fst (-n)-ψ.snd n)

/-- Both rectangular Fourier errors split into the proved nonlinear factors and two spectral errors. -/
theorem sourceBirkhoff_fourier_error_decomposition
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (n : ℤ) :
    let e := fun sign => sourceBirkhoffWeightedCoordinate hp hp1 n s sign ψ-
      sourceGapWeightedEtaTerminalCoordinate hp hp1 n sign ψ
    sourceBirkhoffX hp hp1 n s ψ-(sourceBirkhoffFourier ψ).1 n =
      (e 1+e (-1)-4*sourceEtaMidpointFourierError hp hp1 ψ n)/(Real.sqrt 8:ℂ) ∧
    sourceBirkhoffY hp hp1 n s ψ-(sourceBirkhoffFourier ψ).2 n =
      (e 1-e (-1)-4*I*sourceEtaSineFourierError hp hp1 ψ n)/((Real.sqrt 8:ℂ)*I) := by
  have hs : (Real.sqrt 8:ℂ) = 2*(Real.sqrt 2:ℂ) := by
    have h : Real.sqrt 8 = 2*Real.sqrt 2 := by
      rw [show (8:ℝ)=4*2 by norm_num,Real.sqrt_mul (by norm_num)]
      have hs4 : Real.sqrt 4 = 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 4),Real.sqrt_nonneg 4]
      rw [hs4]
    exact_mod_cast h
  have hn : (Real.sqrt 2:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  dsimp only
  simp only [sourceBirkhoffX,sourceBirkhoffY,sourceBirkhoffFourier_fst,sourceBirkhoffFourier_snd,
    sourceGapWeightedEtaTerminalCoordinate,sourceEtaMidpointFourierError,sourceEtaSineFourierError,
    sourceDirichletMidpointDisplacement_apply,sourceStandardRootMidpoint,hs]
  constructor <;> field_simp [hn] <;> ring_nf
  simp [I_sq]
  ring

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- H2 membership of the two literal spectral errors suffices for the actual Fourier remainder. -/
theorem birkhoff_fourier_h2_of_spectral_errors
    (a : realTypeSobolevSourceLocus)
    (A B : WeightedCoeff (Weight.sobolev 2) 2)
    (hA : ∀ n, A.val n = sourceEtaMidpointFourierError (by simp) (by norm_num) (sobolevSourceInclusion a.val) n)
    (hB : ∀ n, B.val n = sourceEtaSineFourierError (by simp) (by norm_num) (sobolevSourceInclusion a.val) n) :
    ∃ E : WeightedCoeff (Weight.sobolev 2) 2 × WeightedCoeff (Weight.sobolev 2) 2,
      ∀ n, (E.1.val n = (sourceBirkhoffMap (by simp) (by norm_num) s (sobolevSourceInclusion a.val)).1 n-
          (sourceBirkhoffFourier (sobolevSourceInclusion a.val)).1 n) ∧
        (E.2.val n = (sourceBirkhoffMap (by simp) (by norm_num) s (sobolevSourceInclusion a.val)).2 n-
          (sourceBirkhoffFourier (sobolevSourceInclusion a.val)).2 n) := by
  obtain ⟨M,_,h⟩ := D.birkhoff_minus_spectral_terminal_uniform_physical_H1_ball ‖sourcePhysicalH1Coordinates a.val‖
  obtain ⟨u,hu,_⟩ := h a le_rfl 1 (Or.inl rfl)
  obtain ⟨v,hv,_⟩ := h a le_rfl (-1) (Or.inr rfl)
  let X := ((1:ℂ)/(Real.sqrt 8:ℂ)) • (u+v-(4:ℂ) • A)
  let Y := ((1:ℂ)/((Real.sqrt 8:ℂ)*I)) • (u-v-(4*I) • B)
  refine ⟨(X,Y),?_⟩
  intro n
  have he := sourceBirkhoff_fourier_error_decomposition (by simp) (by norm_num) (sobolevSourceInclusion a.val) s n
  rw [(D.coordinates _ (D.real_subset a.property) n).1,
    (D.coordinates _ (D.real_subset a.property) n).2]
  constructor
  · rw [he.1]
    simp only [X,WeightedCoeff.smul_val,WeightedCoeff.sub_val,WeightedCoeff.add_val,hu,hv,hA,Complex.ofReal_one,Complex.ofReal_neg]
    ring
  · rw [he.2]
    simp only [Y,WeightedCoeff.smul_val,WeightedCoeff.sub_val,hu,hv,hB,Complex.ofReal_one,Complex.ofReal_neg]
    ring

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
