import NLS.KdV.HillDiscriminantGardnerCommutation
import NLS.KdV.HillDiscriminantJointCotangent
import NLS.Poisson.GardnerHamiltonianDirection
import NLS.ComplexAnalysis.BilinearCircleIntegral

/-! Weighted contour integrals of the ACTUAL discriminant cotangent
pair to zero under the Gardner bivector. The resulting Hamiltonian
directions preserve every discriminant to first order. This does not
identify these cotangents with the gradients of the action variables. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.KdV

def hillHminusDiscriminantContourCotangent (q : PeriodOneHminusOne)
    (w : ℂ → ℂ) (c : ℂ) (R : ℝ) : PeriodOneHminusOne →L[ℂ] ℂ :=
  ∮ μ in C(c,R), w μ • hillHminusDiscriminantCotangent μ q

theorem hillHminusDiscriminantCotangents_Gardner_commute
    (q : PeriodOneHminusOne) (μ ν : ℂ) :
    NLS.Poisson.gardnerCotangentBivector
      (hillHminusDiscriminantCotangent μ q) (hillHminusDiscriminantCotangent ν q)=0 :=
  hillHminusDiscriminants_Gardner_commute q μ ν

theorem hillHminusDiscriminantContourCotangents_Gardner_commute
    (q : PeriodOneHminusOne) (w v : ℂ → ℂ) (c d : ℂ) (R S : ℝ)
    (hw : CircleIntegrable (fun μ => w μ • hillHminusDiscriminantCotangent μ q) c R)
    (hv : CircleIntegrable (fun ν => v ν • hillHminusDiscriminantCotangent ν q) d S) :
    NLS.Poisson.gardnerCotangentBivector
      (hillHminusDiscriminantContourCotangent q w c R)
      (hillHminusDiscriminantContourCotangent q v d S)=0 := by
  rw [hillHminusDiscriminantContourCotangent,hillHminusDiscriminantContourCotangent,
    NLS.ComplexAnalysis.bilinear_circleIntegral _ hw hv]
  simp only [map_smul,smul_apply,
    hillHminusDiscriminantCotangents_Gardner_commute,smul_zero]
  simp [circleIntegral]

theorem hillHminusDiscriminantContourDirection_isospectral
    (q : PeriodOneHminusOne) (w : ℂ → ℂ) (c : ℂ) (R : ℝ) (μ : ℂ)
    (hw : CircleIntegrable (fun ν => w ν • hillHminusDiscriminantCotangent ν q) c R) :
    (fderiv ℂ (fun p => hillHminusDiscriminant p μ) q)
      (NLS.Poisson.gardnerHamiltonianDirection (hillHminusDiscriminantContourCotangent q w c R))=0 := by
  rw [NLS.Poisson.apply_gardnerHamiltonianDirection]
  change NLS.Poisson.gardnerCotangentBivector (hillHminusDiscriminantCotangent μ q)
    (∮ ν in C(c,R), w ν • hillHminusDiscriminantCotangent ν q)=0
  rw [NLS.ComplexAnalysis.map_circleIntegral _ hw]
  simp only [map_smul,hillHminusDiscriminantCotangents_Gardner_commute,smul_zero]
  simp [circleIntegral]

end NLS.KdV
