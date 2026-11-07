import NLS.Articles.KdVPseudomeasures.OriginalHillRoughFrequencyGrowth

/-! Cubic growth alone makes the genuine rough frequencies tend to
positive infinity. No uniform o(1) assertion is used. -/
noncomputable section
open Filter Topology NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem hillRoughKdVFrequency_tendsto_atTop (q : HillRealMeanZeroSource) :
    Tendsto (fun j : ℕ => hillRoughKdVFrequency ⟨j+1,Nat.succ_pos j⟩ q) atTop atTop := by
  let a : ℝ := (2*Real.pi)^3
  let C : ℝ := ‖hillRoughKdVRenormalizedFrequencySequence ⊤ q‖
  have ha : 0<a := by dsimp [a]; positivity
  have hC : 0≤C := norm_nonneg _
  have hx : Tendsto (fun j : ℕ => (j:ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  apply tendsto_atTop_mono' (l := atTop) _ hx
  filter_upwards [hx.eventually (eventually_ge_atTop ((C+1)/a))] with j hj
  let n : ℕ+ := ⟨j+1,Nat.succ_pos j⟩
  let x : ℝ := (j:ℝ)+1
  have hx1 : 1≤x := by dsimp [x]; have hj0 := Nat.cast_nonneg (α := ℝ) j; linarith
  have hax : C+1≤a*x := by
    have hh := (div_le_iff₀ ha).mp hj
    simpa only [x,mul_comm] using hh
  have hx2 : x≤x^2 := by nlinarith
  have hax2 : C+1≤a*x^2 := hax.trans (mul_le_mul_of_nonneg_left hx2 ha.le)
  have hrem := hillRoughKdVFrequency_remainder_bound q n
  have he : ((hillRoughKdVFrequency n q-a*x^3:ℝ):ℂ)=
      (hillRoughKdVFrequency n q:ℂ)-(2*(Real.pi:ℂ)*(n:ℤ))^3 := by
    dsimp [a,x,n]
    push_cast
    ring
  rw [← he,Complex.norm_real,Real.norm_eq_abs] at hrem
  have hnreal : (n:ℝ)=x := by dsimp [n,x]; simp only [Nat.cast_add,Nat.cast_one]
  rw [hnreal] at hrem
  have hlo := (abs_le.mp hrem).1
  change x≤hillRoughKdVFrequency n q
  nlinarith [mul_le_mul_of_nonneg_right hax2 (by linarith : (0:ℝ)≤x)]

end NLS.Articles.KdVPseudomeasures
