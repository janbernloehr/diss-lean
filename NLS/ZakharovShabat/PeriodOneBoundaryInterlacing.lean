import NLS.ZakharovShabat.FiniteSourceInterlacing
import NLS.ZakharovShabat.RealTypeSourceApproximation

/-! # Ordinary source boundary interlacing, Lemma 9.1(iii)
Symmetric real-type Fourier approximants satisfy the indexed inequalities.
Continuity of every source boundary coordinate and original periodic endpoint
passes those inequalities to all real-type potentials at every finite p>1.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Each original periodic left endpoint is continuous on the source space at real type. -/
theorem continuousAt_canonicalPeriodicLeft_periodOne_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    ContinuousAt (fun ψ : CoeffPair p =>
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ := by
  let F : CoeffPair p →L[ℂ] pairParitySubspace (p := p) 0 :=
    (periodOnePotential (p := p)).codRestrict _ periodOnePotential_mem
  exact (continuousAt_canonicalPeriodicLeft_of_realType hp hp1 (F φ)
    (isRealType_periodOnePotential φ hφ) n).comp F.continuous.continuousAt

/-- Each original periodic right endpoint is continuous on the source space at real type. -/
theorem continuousAt_canonicalPeriodicRight_periodOne_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    ContinuousAt (fun ψ : CoeffPair p =>
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ := by
  let F : CoeffPair p →L[ℂ] pairParitySubspace (p := p) 0 :=
    (periodOnePotential (p := p)).codRestrict _ periodOnePotential_mem
  exact (continuousAt_canonicalPeriodicRight_of_realType hp hp1 (F φ)
    (isRealType_periodOnePotential φ hφ) n).comp F.continuous.continuousAt

/-- Lemma 9.1(iii): each ordinary source boundary root lies in its original indexed periodic gap. -/
theorem canonicalPeriodOneBoundaryRoots_mem_gap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    (canonicalPeriodOneBoundaryRoots hp hp1 b φ n).re ∈
      Icc (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re := by
  let u (N : ℕ) : CoeffPair p := CoeffPair.ofFinsupp (sourceTruncationCoefficients φ N)
  have hu : Tendsto u atTop (𝓝 φ) := tendsto_ofFinsupp_sourceTruncationCoefficients hp φ
  have hL := (continuousAt_canonicalPeriodicLeft_periodOne_of_realType hp hp1 φ hφ n).tendsto.comp hu
  have hR := (continuousAt_canonicalPeriodicRight_periodOne_of_realType hp hp1 φ hφ n).tendsto.comp hu
  have hb := (continuousAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 b φ hφ n).tendsto.comp hu
  have h (N : ℕ) := canonicalPeriodOneBoundaryRoots_mem_gap_finite hp hp1 b
    (sourceTruncationCoefficients φ N) (sourceTruncationCoefficients_realType φ hφ N) n
  exact ⟨le_of_tendsto_of_tendsto' (continuous_re.continuousAt.tendsto.comp hL)
      (continuous_re.continuousAt.tendsto.comp hb) (fun N => (h N).1),
    le_of_tendsto_of_tendsto' (continuous_re.continuousAt.tendsto.comp hb)
      (continuous_re.continuousAt.tendsto.comp hR) (fun N => (h N).2)⟩

/-- Both ordinary boundary sequences interlace simultaneously with the original periodic endpoints. -/
theorem canonicalPeriodOneBoundaryRoots_interlacing (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    let l := (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
    let r := (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n).re ∈ Icc l r ∧
      (canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ n).re ∈ Icc l r :=
  ⟨canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 .dirichlet φ hφ n,
    canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 .neumann φ hφ n⟩

/-- The literal source interlacing chain includes strict separation from neighboring gaps. -/
theorem canonicalPeriodOneBoundaryRoots_interlacing_chain (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    let L := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
    let R := canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    (R (n-1)).re < (L n).re ∧ (L n).re ≤ μ.re ∧ μ.re ≤ (R n).re ∧ (R n).re < (L (n+1)).re := by
  have h := canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 b φ hφ n
  exact ⟨canonicalPeriodicRight_re_lt_left_of_lt hp hp1 _ (periodOnePotential_mem φ)
      (isRealType_periodOnePotential φ hφ) (by omega), h.1, h.2,
    canonicalPeriodicRight_re_lt_left_of_lt hp hp1 _ (periodOnePotential_mem φ)
      (isRealType_periodOnePotential φ hφ) (by omega)⟩

/-- A collapsed original source gap identifies either ordinary boundary root with its endpoint. -/
theorem canonicalPeriodOneBoundaryRoots_eq_of_collapsed_gap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ)
    (he : canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n =
      canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n) :
    canonicalPeriodOneBoundaryRoots hp hp1 b φ n =
      canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n := by
  apply Complex.ext
  · have h := canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 b φ hφ n
    rw [← he] at h
    exact le_antisymm h.2 h.1
  · exact (canonicalPeriodOneBoundaryRoots_im_eq_zero hp hp1 b φ hφ n).trans
      (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 _ (periodOnePotential_mem φ)
        (isRealType_periodOnePotential φ hφ) n).1.symm

/-- The original periodic discriminant has the source signed level at every ordinary boundary root. -/
theorem signed_discriminant_periodOneBoundaryRoot_ge_two (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    2 ≤ (-1 : ℝ)^n * (canonicalDiscriminant hp (periodOnePotential φ)
      (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)).re := by
  have h := signed_discriminant_ge_two_on_canonicalGap hp hp1 _ (periodOnePotential_mem φ)
    (isRealType_periodOnePotential φ hφ) n _ (canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 b φ hφ n)
  have he : (((canonicalPeriodOneBoundaryRoots hp hp1 b φ n).re : ℝ) : ℂ) =
      canonicalPeriodOneBoundaryRoots hp hp1 b φ n := by
    apply Complex.ext
    · rfl
    · simpa only [ofReal_im] using (canonicalPeriodOneBoundaryRoots_im_eq_zero hp hp1 b φ hφ n).symm
  rwa [he] at h

end NLS.ZakharovShabat
