import NLS.KdV.HillOriginalBirkhoffMap
import NLS.KdV.HillAbelianCartesianNormalization

/-! # The fixed global real Birkhoff map has the original complex normalization

The canonical real pair has Y=-Im(Cartesian), so (X-iY)/sqrt(2) is exactly
the original sqrt(action) Abelian coordinate, including every closed gap.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.KdV

def hillOriginalBirkhoffAbelianCoordinate (q : hillRealMeanZeroSourceSubmodule) (n : ℕ+) : ℂ :=
  let p := (hillOriginalBirkhoffMap q).val ((n : ℕ)-1)
  ((p.1 : ℂ)-I*(p.2 : ℂ))/(Real.sqrt 2 : ℂ)

theorem hillOriginalBirkhoffAbelianCoordinate_eq_original
    (q : hillRealMeanZeroSourceSubmodule) (n : ℕ+) :
    hillOriginalBirkhoffAbelianCoordinate q n=
      hillDirichletAbelianCoordinate q.val.val q.val.property.1 q.val.property.2 n n.pos := by
  have hn : (⟨(n : ℕ)-1+1,by have := n.pos; omega⟩ : ℕ+)=n := by
    apply Subtype.ext
    change (n : ℕ)-1+1=(n : ℕ)
    have := n.pos
    omega
  unfold hillOriginalBirkhoffAbelianCoordinate
  rw [hillOriginalBirkhoffMap_coordinates,hn]
  have hpair : (hillOriginalBirkhoffX q n : ℂ)-I*(hillOriginalBirkhoffY q n : ℂ)=
      hillSpectralCartesian q.val.val q.val.property.1 q.val.property.2 n n.pos := by
    apply Complex.ext <;> simp [hillOriginalBirkhoffX,hillOriginalBirkhoffY]
  change ((hillOriginalBirkhoffX q n : ℂ)-I*(hillOriginalBirkhoffY q n : ℂ))/(Real.sqrt 2 : ℂ)=_
  rw [hpair,hillSpectralCartesian_eq_sqrt_two_mul_abelian
    (⟨q.val.val,q.val.property⟩ : RealPeriodOneHillPotential) n n.pos]
  exact mul_div_cancel_left₀ _ (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2)).ne')

theorem hillBirkhoffAbelian_rough_map_agreement
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (U : Set PeriodOneHminusOne)
    (hZp : ∀ p : RealPeriodOneHillPotential, (hillPhysicalHminusEmbedding p).val∈U → ∀ j : ℤ,
      (Z (hillPhysicalHminusEmbedding p).val).val j=
        hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j)
    (q : hillRealMeanZeroSourceSubmodule) (hq : hillOriginalHminusSource q.val.val∈U) (n : ℕ+) :
    (Z (hillOriginalHminusSource q.val.val)).val (n : ℤ)=hillOriginalBirkhoffAbelianCoordinate q n := by
  let p : RealPeriodOneHillPotential := ⟨q.val.val,q.val.property⟩
  have hpU : (hillPhysicalHminusEmbedding p).val∈U := by
    simpa only [← hillOriginalHminusSource_eq_physical] using hq
  have hh := hZp p hpU (n : ℤ)
  change (Z (hillOriginalHminusSource q.val.val)).val (n : ℤ)=_
  change (Z (hillOriginalHminusSource p.val)).val (n : ℤ)=_
  rw [hillOriginalHminusSource_eq_physical]
  exact hh.trans ((hillAbelianRawCoordinateSequence_original_nat p n).trans
    (hillOriginalBirkhoffAbelianCoordinate_eq_original q n).symm)

end NLS.KdV
