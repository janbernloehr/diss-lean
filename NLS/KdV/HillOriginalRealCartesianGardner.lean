import NLS.KdV.HillOriginalRealBirkhoffCoordinates
import NLS.Poisson.RealCartesianSignedMatrix

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV

/-- The SAME fixed physical real pair (Re Z,-Im Z) has analytic native
germs carrying the canonical real Gardner matrix at EVERY original source,
including every low and collapsed gap. No canonical-map premise is supplied. -/
theorem exists_hillOriginalRealBirkhoff_canonical_germs
    (q : hillRealMeanZeroSourceSubmodule) :
    ∃ X Y : ℕ+ → PeriodOneHminusOne → ℂ,
      (∀ n : ℕ+,
        AnalyticAt ℂ (X n) (hillOriginalHminusSource q.val.val) ∧
        AnalyticAt ℂ (Y n) (hillOriginalHminusSource q.val.val) ∧
        ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q.val.val,q.val.property⟩ : RealPeriodOneHillPotential),
          X n (hillOriginalHminusSource p.val) =
            ((hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos).re : ℂ) ∧
          Y n (hillOriginalHminusSource p.val) =
            (-(hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos).im : ℂ)) ∧
      ∀ n m : ℕ+,
        NLS.Poisson.hminusGardnerBracket (X n) (X m) (hillOriginalHminusSource q.val.val) = 0 ∧
        NLS.Poisson.hminusGardnerBracket (X n) (Y m) (hillOriginalHminusSource q.val.val) =
          (if (n : ℕ) = (m : ℕ) then 1 else 0) ∧
        NLS.Poisson.hminusGardnerBracket (Y n) (X m) (hillOriginalHminusSource q.val.val) =
          -(if (n : ℕ) = (m : ℕ) then 1 else 0) ∧
        NLS.Poisson.hminusGardnerBracket (Y n) (Y m) (hillOriginalHminusSource q.val.val) = 0 := by
  let Q : RealPeriodOneHillPotential := ⟨q.val.val,q.val.property⟩
  let x := hillOriginalHminusSource q.val.val
  have hmean : Q.val.val 0 = 0 := (mem_hillRealMeanZeroSourceSubmodule q.val).mp q.property
  obtain ⟨Z,hZ,hM⟩ := exists_hillOriginal_signedCartesian_hminus_Gardner_matrix_all_gaps Q hmean
  let X : ℕ+ → PeriodOneHminusOne → ℂ := fun n p => (1/2 : ℂ) • (Z true n p+Z false n p)
  let Y : ℕ+ → PeriodOneHminusOne → ℂ := fun n p => (I/2) • (Z true n p-Z false n p)
  have hDX (n : ℕ+) : fderiv ℂ (X n) x =
      (1/2 : ℂ) • (fderiv ℂ (Z true n) x+fderiv ℂ (Z false n) x) :=
    (((hZ true n).1.differentiableAt.hasFDerivAt.add
      (hZ false n).1.differentiableAt.hasFDerivAt).const_smul (1/2 : ℂ)).fderiv
  have hDY (n : ℕ+) : fderiv ℂ (Y n) x =
      (I/2) • (fderiv ℂ (Z true n) x-fderiv ℂ (Z false n) x) :=
    (((hZ true n).1.differentiableAt.hasFDerivAt.sub
      (hZ false n).1.differentiableAt.hasFDerivAt).const_smul (I/2)).fderiv
  refine ⟨X,Y,?_,?_⟩
  · intro n
    refine ⟨((hZ true n).1.add (hZ false n).1).const_smul (c := (1/2 : ℂ)),
      ((hZ true n).1.sub (hZ false n).1).const_smul (c := (I/2 : ℂ)),?_⟩
    filter_upwards [(hZ true n).2,(hZ false n).2] with p hp hn
    dsimp only [X,Y]
    rw [hp,hn]
    simp only [hillSignedSpectralCartesian,ite_true,Bool.false_eq_true,ite_false,smul_eq_mul]
    constructor <;> apply Complex.ext <;> simp <;> ring
  · intro n m
    let B := NLS.Poisson.gardnerCotangentBivector
    have hLG : B (fderiv ℂ (Z true n) x) (fderiv ℂ (Z true m) x) = 0 := by
      have hh := hM true true n m
      have he : hillOriginalComplexGardnerMatrixEntry true true n m = 0 := by simp [hillOriginalComplexGardnerMatrixEntry]
      rw [he] at hh
      exact hh
    have hLH : B (fderiv ℂ (Z true n) x) (fderiv ℂ (Z false m) x) =
        2*I*(if (n : ℕ) = (m : ℕ) then 1 else 0) := hM true false n m
    have hWG : B (fderiv ℂ (Z false n) x) (fderiv ℂ (Z true m) x) =
        -(2*I)*(if (n : ℕ) = (m : ℕ) then 1 else 0) := hM false true n m
    have hWH : B (fderiv ℂ (Z false n) x) (fderiv ℂ (Z false m) x) = 0 := by
      have hh := hM false false n m
      have he : hillOriginalComplexGardnerMatrixEntry false false n m = 0 := by simp [hillOriginalComplexGardnerMatrixEntry]
      rw [he] at hh
      exact hh
    change B (fderiv ℂ (X n) x) (fderiv ℂ (X m) x) = 0 ∧
      B (fderiv ℂ (X n) x) (fderiv ℂ (Y m) x) = _ ∧
      B (fderiv ℂ (Y n) x) (fderiv ℂ (X m) x) = _ ∧
      B (fderiv ℂ (Y n) x) (fderiv ℂ (Y m) x) = 0
    rw [hDX,hDX,hDY,hDY]
    exact NLS.Poisson.realCartesianMatrix_of_signed B _ _ _ _ _ hLG hLH hWG hWH

end NLS.KdV
