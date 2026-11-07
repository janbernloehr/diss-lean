import NLS.KdV.HillFrequencyMidpointUniformLowerBound
import NLS.KdV.HillHminusOneCanonicalGapSquares

/-! Exact conversion of original squared Hill-gap bounds into the
gap-index-weighted Dirac-gap decay needed by the frequency moment series. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch

theorem norm_canonical_gapSquare_eq_midpoint_gap (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (n : ℕ+) :
    ‖hillHminusCanonicalGapSquare n q‖ =
      4*‖sourceStandardRootMidpoint (by simp) (by norm_num) (P.sourcePsi q) (n:ℤ)‖^2*
        ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi q) (n:ℤ)‖^2 := by
  let B := P.parent.parent.miuraBall
  rw [B.canonical_gapSquare_eq n q (P.parent.subset (P.subset hq)).1]
  change ‖(canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) (n:ℤ))^2*
        (2*sourceStandardRootMidpoint (by simp) (by norm_num) (P.sourcePsi q) (n:ℤ))^2‖ = _
  rw [sourcePeriodicGapDisplacement_apply]
  simp only [norm_mul,norm_pow,Complex.norm_ofNat]
  ring

/-- The exponent 1-2r is strictly positive throughout the original
endpoint range. The estimate keeps every positive mode, including collapse. -/
theorem weighted_dirac_gap_power_bound (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (n : ℕ+)
    (r a C : ℝ) (ha : 0 < a)
    (hmid : a*(n:ℝ) ≤ ‖sourceStandardRootMidpoint (by simp) (by norm_num) (P.sourcePsi q) (n:ℤ)‖)
    (hgap : ‖hillHminusCanonicalGapSquare n q‖ ≤ C^2*(1+(n:ℝ))^(2*r)) :
    (n:ℝ)*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi q) (n:ℤ)‖^2 ≤
      (C^2/(2*a^2))/(1+(n:ℝ))^(1-2*r) := by
  let g : ℝ := ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi q) (n:ℤ)‖
  let t : ℝ := ‖sourceStandardRootMidpoint (by simp) (by norm_num) (P.sourcePsi q) (n:ℤ)‖
  have hn : (0:ℝ)<n := by exact_mod_cast n.pos
  have hn1 : (1:ℝ)≤n := by exact_mod_cast n.property
  have hbound : 4*t^2*g^2 ≤ C^2*(1+(n:ℝ))^(2*r) := by
    rw [P.norm_canonical_gapSquare_eq_midpoint_gap q hq n] at hgap
    exact hgap
  have hsq : (a*(n:ℝ))^2 ≤ t^2 := pow_le_pow_left₀ (by positivity) hmid 2
  have hfirst : g^2 ≤ C^2*(1+(n:ℝ))^(2*r)/(4*a^2*(n:ℝ)^2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hle := mul_le_mul_of_nonneg_right hsq (by positivity : 0≤4*g^2)
    nlinarith only [hle,hbound]
  have hratio : (1+(n:ℝ))^(2*r)/(n:ℝ) ≤ 2/(1+(n:ℝ))^(1-2*r) := by
    apply (div_le_div_iff₀ hn (Real.rpow_pos_of_pos (by positivity) _)).mpr
    rw [← Real.rpow_add (by positivity : (0:ℝ)<1+(n:ℝ)),
      show 2*r+(1-2*r)=1 by ring,Real.rpow_one]
    linarith
  calc
    (n:ℝ)*g^2 ≤ (n:ℝ)*(C^2*(1+(n:ℝ))^(2*r)/(4*a^2*(n:ℝ)^2)) :=
      mul_le_mul_of_nonneg_left hfirst hn.le
    _ = (C^2/(4*a^2))*((1+(n:ℝ))^(2*r)/(n:ℝ)) := by field_simp
    _ ≤ (C^2/(4*a^2))*(2/(1+(n:ℝ))^(1-2*r)) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

end NLS.KdV.HillProductEquationPatch
