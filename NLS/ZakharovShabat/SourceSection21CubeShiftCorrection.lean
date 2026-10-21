import NLS.ZakharovShabat.SourceSection19Primitive

noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Cubing the original normalization shift retains an imaginary constant. -/
theorem cube_sub_imaginary_shift (f a : ℂ) :
    (f-I*a)^3 = f^3-3*I*f^2*a-3*f*a^2+I*a^3 := by
  ring_nf
  simp only [I_sq,I_pow_three]
  ring

/-- The literal p97 algebraic expansion fails whenever its index shift is nonzero. -/
theorem cube_sub_imaginary_shift_ne_printed (f a : ℂ) (ha : a ≠ 0) :
    (f-I*a)^3 ≠ f^3-3*I*f^2*a-3*f*a^2+a^3 := by
  rw [cube_sub_imaginary_shift]
  intro he
  have hz : (I-1)*a^3 = 0 := by linear_combination he
  have hi : (I:ℂ)-1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  exact (mul_ne_zero hi (pow_ne_zero _ ha)) hz

namespace SourceSection19Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W U : Set (CoeffPair p)} (Q : SourceSection19Data hp hp1 W U)
include Q

/-- The correct cube identity for the retained primitive throughout its filled spectral domain. -/
theorem cube_index_shift (ψ : CoeffPair p) (hψ : ψ ∈ U) (n : ℤ) (z : ℂ)
    (hz : z ∈ sourceOpenGapComplement hp hp1 ψ) :
    let f := sourceFullAbelianPrimitive hp hp1 W n (z,ψ)
    (sourceFullAbelianPrimitive hp hp1 W 0 (z,ψ))^3 =
      f^3-3*I*f^2*((Real.pi:ℂ)*n)-3*f*((Real.pi:ℂ)*n)^2+I*((Real.pi:ℂ)*n)^3 := by
  dsimp only
  have he : sourceFullAbelianPrimitive hp hp1 W 0 (z,ψ) =
      sourceFullAbelianPrimitive hp hp1 W n (z,ψ)-I*((Real.pi:ℂ)*n) := by
    rw [Q.index_shift ψ hψ n z hz]
    ring
  rw [he]
  exact cube_sub_imaginary_shift _ _

/-- The printed p97 cube shift fails already at the actual zero source,
for every nonzero signed normalization index and every spectral argument. -/
theorem zero_cube_index_shift_ne_printed (n : ℤ) (hn : n ≠ 0) (z : ℂ) :
    let f := sourceFullAbelianPrimitive hp hp1 W n (z,0)
    (sourceFullAbelianPrimitive hp hp1 W 0 (z,0))^3 ≠
      f^3-3*I*f^2*((Real.pi:ℂ)*n)-3*f*((Real.pi:ℂ)*n)^2+((Real.pi:ℂ)*n)^3 := by
  dsimp only
  rw [(Q.zero 0 z).1,(Q.zero n z).1]
  simp only [Int.cast_zero,mul_zero,add_zero]
  have ha : (Real.pi:ℂ)*n ≠ 0 := mul_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (by exact_mod_cast hn)
  have h := cube_sub_imaginary_shift_ne_printed (-I*z+I*(Real.pi:ℂ)*n) ((Real.pi:ℂ)*n) ha
  convert h using 1
  ring

end SourceSection19Data
end NLS.ZakharovShabat
