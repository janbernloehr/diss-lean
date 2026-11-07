import NLS.SequenceSpaces.DoublingProduct
import NLS.SequenceSpaces.ConvolutionMajorants
import NLS.SequenceSpaces.ExponentEmbedding
import NLS.SequenceSpaces.PuncturedLattice

/-! The diagonal, reciprocal convolution and inverse-index tail form
an actual lp majorant for weighted moment rows, for every p>1. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Coeff

def squaredGapMagnitude (g : Coeff 2) : Coeff 1 :=
  doublingProduct (p := 1) (magnitude g) (magnitude g)

theorem squaredGapMagnitude_apply (g : Coeff 2) (k : ℤ) :
    squaredGapMagnitude g k=(‖g k‖^2:ℝ) := by
  simp only [squaredGapMagnitude,doublingProduct_apply,magnitude_apply,← ofReal_mul,pow_two]

theorem norm_squaredGapMagnitude (g : Coeff 2) : ‖squaredGapMagnitude g‖=‖g‖^2 := by
  rw [squaredGapMagnitude,norm_doublingProduct_self (by norm_num) (by norm_num),norm_magnitude]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def squaredGapMomentMajorant (hp : 1 < p) (g : Coeff 2) : Coeff p :=
  magnitude (exponentInclusion hp.le (squaredGapMagnitude g))+
    magnitude (convolution (magnitude (puncturedLattice p hp)) (magnitude (squaredGapMagnitude g)))+
    ((2*‖squaredGapMagnitude g‖:ℝ):ℂ) • magnitude (puncturedLattice p hp)

theorem norm_squaredGapMomentMajorant_apply (hp : 1 < p) (g : Coeff 2) (k : ℤ) :
    ‖squaredGapMomentMajorant hp g k‖ =
      ‖squaredGapMagnitude g k‖+
        ‖convolution (magnitude (puncturedLattice p hp)) (magnitude (squaredGapMagnitude g)) k‖+
        2*‖squaredGapMagnitude g‖*‖puncturedLattice p hp k‖ := by
  have he : squaredGapMomentMajorant hp g k =
      ((‖squaredGapMagnitude g k‖+
        ‖convolution (magnitude (puncturedLattice p hp)) (magnitude (squaredGapMagnitude g)) k‖+
        2*‖squaredGapMagnitude g‖*‖puncturedLattice p hp k‖:ℝ):ℂ) := by
    simp only [squaredGapMomentMajorant,lp.coeFn_add,Pi.add_apply,magnitude_apply,
      exponentInclusion_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
    push_cast
    rfl
  rw [he,Complex.norm_real,Real.norm_of_nonneg (by positivity)]

theorem norm_squaredGapMomentMajorant_le (hp : 1 < p) (g : Coeff 2) :
    ‖squaredGapMomentMajorant hp g‖ ≤ (1+3*‖puncturedLattice p hp‖)*‖g‖^2 := by
  let b := squaredGapMagnitude g
  let κ := puncturedLattice p hp
  have he := norm_exponentInclusion_le hp.le b
  have hc := norm_convolution_le (magnitude κ) (magnitude b)
  simp only [norm_magnitude] at hc
  have h₁ := norm_add_le (magnitude (exponentInclusion hp.le b))
    (magnitude (convolution (magnitude κ) (magnitude b)))
  have h₂ := norm_add_le
    (magnitude (exponentInclusion hp.le b)+magnitude (convolution (magnitude κ) (magnitude b)))
    (((2*‖b‖:ℝ):ℂ) • magnitude κ)
  simp only [norm_magnitude,norm_smul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ 2*‖b‖)] at h₁ h₂
  change ‖squaredGapMomentMajorant hp g‖ ≤ _ at h₂
  have hb : ‖b‖=‖g‖^2 := norm_squaredGapMagnitude g
  rw [← hb]
  nlinarith

end NLS.Coeff
