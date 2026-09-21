import NLS.ZakharovShabat.RealBoundaryPotentialPaths
import NLS.ZakharovShabat.ClassicalBoundaryGapBound
import NLS.ZakharovShabat.RealGapDiscriminantLevels
import NLS.ZakharovShabat.CanonicalBoundaryFree
import NLS.ZakharovShabat.CanonicalPeriodicFree
import NLS.ComplexAnalysis.SeparatedIntervalPaths

/-! # Indexed boundary interlacing for compatible continuous potentials
The real scaling path starts at the signed free lattice. Actual boundary
roots stay in the union of original periodic gaps, so continuous midpoint
barriers preserve their signed gap index all the way to the given potential.
The two coefficient realizations remain distinct throughout the argument.
-/

noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.ComplexAnalysis
open scoped ComplexConjugate
namespace NLS.ZakharovShabat

/-- The canonical boundary root belongs to the original periodic gap with the same signed index. -/
theorem canonicalBoundaryRoots_mem_gap_of_continuous (b : BoundaryCondition)
    (φ : pairParitySubspace (p := 2) 0) (hφ : IsRealType φ.val)
    (ψ : dirichletSubspace (p := 2)) (hψ : IsRealType ψ.val) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ.val =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hΨ : physicalBase ψ.val =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hr : ∀ t, (Φ t).2 = conj (Φ t).1) (n : ℤ) :
    (b.canonicalRoots (by simp) (by norm_num) ψ.val ψ.property n).re ∈
      Icc (canonicalPeriodicLeft (by simp) (by norm_num) φ.val φ.property n).re
        (canonicalPeriodicRight (by simp) (by norm_num) φ.val φ.property n).re := by
  let L : ℝ → ℤ → ℝ := fun t k => (canonicalPeriodicLeft (by simp) (by norm_num)
    (realPotentialPath φ t).val (realPotentialPath φ t).property k).re
  let R : ℝ → ℤ → ℝ := fun t k => (canonicalPeriodicRight (by simp) (by norm_num)
    (realPotentialPath φ t).val (realPotentialPath φ t).property k).re
  let y : ℝ → ℝ := fun t => (b.canonicalRoots (by simp) (by norm_num)
    (realBoundaryPotentialPath ψ t).val (realBoundaryPotentialPath ψ t).property n).re
  have hL (k : ℤ) : ContinuousOn (fun t => L t k) (Icc 0 1) :=
    (continuous_re.comp (continuous_canonicalPeriodicLeft_realPotentialPath (by simp) (by norm_num) φ hφ k)).continuousOn
  have hR (k : ℤ) : ContinuousOn (fun t => R t k) (Icc 0 1) :=
    (continuous_re.comp (continuous_canonicalPeriodicRight_realPotentialPath (by simp) (by norm_num) φ hφ k)).continuousOn
  have hy : ContinuousOn y (Icc 0 1) :=
    (continuous_re.comp (continuous_canonicalBoundaryRoots_realBoundaryPotentialPath (by simp) (by norm_num) b ψ hψ n)).continuousOn
  have hLR (t : ℝ) (_ : t ∈ Icc (0 : ℝ) 1) (k : ℤ) : L t k ≤ R t k :=
    re_le_of_complexLexLE ((canonicalPeriodicEndpoints_spec (by simp) (by norm_num)
      (realPotentialPath φ t).val (realPotentialPath φ t).property).2.1 k)
  have hsep (t : ℝ) (_ : t ∈ Icc (0 : ℝ) 1) (i j : ℤ) (hij : i < j) : R t i < L t j :=
    canonicalPeriodicRight_re_lt_left_of_lt (by simp) (by norm_num) (realPotentialPath φ t).val
      (realPotentialPath φ t).property (realPotentialPath_isRealType φ hφ t) hij
  have hmem (t : ℝ) (_ : t ∈ Icc (0 : ℝ) 1) : ∃ k, y t ∈ Icc (L t k) (R t k) := by
    apply exists_canonicalGap_of_boundaryEigenvalue b (realPotentialPath φ t).val
      (realPotentialPath φ t).property (realPotentialPath_isRealType φ hφ t)
      (realBoundaryPotentialPath ψ t).val (realBoundaryPotentialPath ψ t).property ((t : ℂ) • Φ)
      (physicalBase_smul_eq_extend (t : ℂ) φ.val Φ hΦ)
      (physicalBase_smul_eq_extend (t : ℂ) ψ.val Φ hΨ) (realType_curve_ofReal_smul Φ hr t) (y t)
    have hi := b.canonicalRoots_im_eq_zero (by simp) (by norm_num) (realBoundaryPotentialPath ψ t).val
      (realBoundaryPotentialPath ψ t).property (realBoundaryPotentialPath_isRealType ψ hψ t) n
    have he : ((y t : ℝ) : ℂ) = b.canonicalRoots (by simp) (by norm_num)
        (realBoundaryPotentialPath ψ t).val (realBoundaryPotentialPath ψ t).property n := by
      apply Complex.ext
      · rfl
      · simpa only [ofReal_im] using hi.symm
    rw [he]
    exact b.canonicalRoots_mem_spectrum (by simp) (by norm_num) _ _ n
  have hzero : y 0 ∈ Icc (L 0 n) (R 0 n) := by
    simp [y,L,R]
  have hend := mem_interval_on_Icc_of_separated L R y (by norm_num : (0 : ℝ) ≤ 1)
    hL hR hy hLR hsep hmem n hzero 1 (by constructor <;> norm_num)
  simpa only [y,L,R,realPotentialPath_one,realBoundaryPotentialPath_one] using hend

/-- Dirichlet and Neumann coordinates interlace simultaneously with the same original periodic endpoints. -/
theorem canonicalBoundaryRoots_interlacing_of_continuous
    (φ : pairParitySubspace (p := 2) 0) (hφ : IsRealType φ.val)
    (ψ : dirichletSubspace (p := 2)) (hψ : IsRealType ψ.val) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ.val =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hΨ : physicalBase ψ.val =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hr : ∀ t, (Φ t).2 = conj (Φ t).1) (n : ℤ) :
    let l := (canonicalPeriodicLeft (by simp) (by norm_num) φ.val φ.property n).re
    let r := (canonicalPeriodicRight (by simp) (by norm_num) φ.val φ.property n).re
    (BoundaryCondition.canonicalRoots .dirichlet (by simp) (by norm_num) ψ.val ψ.property n).re ∈ Icc l r ∧
      (BoundaryCondition.canonicalRoots .neumann (by simp) (by norm_num) ψ.val ψ.property n).re ∈ Icc l r :=
  ⟨canonicalBoundaryRoots_mem_gap_of_continuous .dirichlet φ hφ ψ hψ Φ hΦ hΨ hr n,
    canonicalBoundaryRoots_mem_gap_of_continuous .neumann φ hφ ψ hψ Φ hΦ hΨ hr n⟩

/-- A collapsed original gap forces either canonical boundary coordinate to equal its unique endpoint. -/
theorem canonicalBoundaryRoots_eq_of_collapsed_gap_of_continuous (b : BoundaryCondition)
    (φ : pairParitySubspace (p := 2) 0) (hφ : IsRealType φ.val)
    (ψ : dirichletSubspace (p := 2)) (hψ : IsRealType ψ.val) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ.val =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hΨ : physicalBase ψ.val =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hr : ∀ t, (Φ t).2 = conj (Φ t).1) (n : ℤ)
    (he : canonicalPeriodicLeft (by simp) (by norm_num) φ.val φ.property n =
      canonicalPeriodicRight (by simp) (by norm_num) φ.val φ.property n) :
    b.canonicalRoots (by simp) (by norm_num) ψ.val ψ.property n =
      canonicalPeriodicLeft (by simp) (by norm_num) φ.val φ.property n := by
  have hb := canonicalBoundaryRoots_mem_gap_of_continuous b φ hφ ψ hψ Φ hΦ hΨ hr n
  rw [← he] at hb
  apply Complex.ext
  · exact le_antisymm hb.2 hb.1
  · exact (b.canonicalRoots_im_eq_zero (by simp) (by norm_num) ψ.val ψ.property hψ n).trans
      (canonicalPeriodicEndpoints_im_eq_zero_of_realType (by simp) (by norm_num) φ.val φ.property hφ n).1.symm

/-- The full neighboring-gap chain holds at every signed boundary index for compatible continuous potentials. -/
theorem canonicalBoundaryRoots_interlacing_chain_of_continuous (b : BoundaryCondition)
    (φ : pairParitySubspace (p := 2) 0) (hφ : IsRealType φ.val)
    (ψ : dirichletSubspace (p := 2)) (hψ : IsRealType ψ.val) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ.val =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hΨ : physicalBase ψ.val =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hr : ∀ t, (Φ t).2 = conj (Φ t).1) (n : ℤ) :
    let L := fun k => (canonicalPeriodicLeft (by simp) (by norm_num) φ.val φ.property k).re
    let R := fun k => (canonicalPeriodicRight (by simp) (by norm_num) φ.val φ.property k).re
    let μ := (b.canonicalRoots (by simp) (by norm_num) ψ.val ψ.property n).re
    R (n-1) < L n ∧ L n ≤ μ ∧ μ ≤ R n ∧ R n < L (n+1) := by
  have hb := canonicalBoundaryRoots_mem_gap_of_continuous b φ hφ ψ hψ Φ hΦ hΨ hr n
  exact ⟨canonicalPeriodicRight_re_lt_left_of_lt (by simp) (by norm_num) φ.val φ.property hφ (by omega),
    hb.1,hb.2,canonicalPeriodicRight_re_lt_next_left (by simp) (by norm_num) φ.val φ.property hφ n⟩

/-- The original periodic discriminant has the source's signed inequality at each canonical boundary root. -/
theorem signed_canonicalDiscriminant_boundaryRoot_ge_two_of_continuous (b : BoundaryCondition)
    (φ : pairParitySubspace (p := 2) 0) (hφ : IsRealType φ.val)
    (ψ : dirichletSubspace (p := 2)) (hψ : IsRealType ψ.val) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ.val =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hΨ : physicalBase ψ.val =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hr : ∀ t, (Φ t).2 = conj (Φ t).1) (n : ℤ) :
    2 ≤ (-1 : ℝ)^n * (canonicalDiscriminant (by simp) φ.val
      (b.canonicalRoots (by simp) (by norm_num) ψ.val ψ.property n)).re := by
  have hb := canonicalBoundaryRoots_mem_gap_of_continuous b φ hφ ψ hψ Φ hΦ hΨ hr n
  have hs := signed_discriminant_ge_two_on_canonicalGap (by simp) (by norm_num) φ.val φ.property hφ n _ hb
  have he : (((b.canonicalRoots (by simp) (by norm_num) ψ.val ψ.property n).re : ℝ) : ℂ) =
      b.canonicalRoots (by simp) (by norm_num) ψ.val ψ.property n := by
    apply Complex.ext
    · rfl
    · simpa only [ofReal_im] using (b.canonicalRoots_im_eq_zero (by simp) (by norm_num) ψ.val ψ.property hψ n).symm
  rwa [he] at hs

/-- The same signed bound holds for the actual monodromy trace of the common physical representative. -/
theorem signed_classicalDiscriminant_boundaryRoot_ge_two_of_continuous (b : BoundaryCondition)
    (φ : pairParitySubspace (p := 2) 0) (hφ : IsRealType φ.val)
    (ψ : dirichletSubspace (p := 2)) (hψ : IsRealType ψ.val) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ.val =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hΨ : physicalBase ψ.val =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hr : ∀ t, (Φ t).2 = conj (Φ t).1) (n : ℤ) :
    2 ≤ (-1 : ℝ)^n * (classicalDiscriminant Φ
      (b.canonicalRoots (by simp) (by norm_num) ψ.val ψ.property n)).re := by
  rw [← canonicalDiscriminant_eq_classical φ.val φ.property Φ hΦ]
  exact signed_canonicalDiscriminant_boundaryRoot_ge_two_of_continuous b φ hφ ψ hψ Φ hΦ hΨ hr n

end NLS.ZakharovShabat
