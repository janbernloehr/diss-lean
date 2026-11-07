import NLS.ComplexAnalysis.QuadraticCauchyUniqueness
import NLS.ComplexAnalysis.AnalyticZeroCount

/-! Uniqueness of the filled root equation for an arbitrary analytic
radicand, including multiple zeros. Dividing by a nonzero analytic
multiplier transforms the equation with the exact multiplier factor. -/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem radicand_equation_homogeneous_eq_zero
    (D H : ℂ → ℂ) (Ω : Set ℂ) (a : ℂ)
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (ha : a ∈ Ω) (hDa : D a = 0)
    (hD : AnalyticOnNhd ℂ D Ω) (hfinite : ∀ z ∈ Ω, analyticOrderAt D z ≠ ⊤)
    (hH : AnalyticOnNhd ℂ H Ω)
    (heq : ∀ z ∈ Ω, D z*deriv H z+(deriv D z/2)*H z = 0) :
    ∀ z ∈ Ω, H z = 0 := by
  let K : ℂ → ℂ := fun z => D z*(H z)^2
  have hKa : K a = 0 := by simp only [K,hDa,zero_mul]
  have hKd (z : ℂ) (hz : z ∈ Ω) : HasDerivAt K 0 z := by
    have hd := (hD z hz).differentiableAt.hasDerivAt.fun_mul
      ((hH z hz).differentiableAt.hasDerivAt.pow 2)
    convert! hd using 1
    simp only [Pi.pow_apply]
    linear_combination -2*H z*(heq z hz)
  have hKzero (z : ℂ) (hz : z ∈ Ω) : K z = 0 := by
    rw [← hKa]
    exact hΩ.is_const_of_deriv_eq_zero hconn
      (fun z hz => (hKd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hKd z hz).deriv) hz ha
  intro z hz
  have ho : analyticOrderAt K z = ⊤ := analyticOrderAt_eq_top.mpr (by
    filter_upwards [hΩ.mem_nhds hz] with w hw
    exact hKzero w hw)
  change analyticOrderAt (D*H^2) z = ⊤ at ho
  rw [analyticOrderAt_mul (hD z hz) ((hH z hz).pow 2)] at ho
  have he : H^2 =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) :=
    analyticOrderAt_eq_top.mp ((ENat.add_eq_top.mp ho).resolve_left (hfinite z hz))
  exact eq_zero_of_pow_eq_zero (show (H z)^2 = 0 from he.eq_of_nhds)

theorem radicand_equation_solution_unique
    (D g H J : ℂ → ℂ) (Ω : Set ℂ) (a : ℂ)
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (ha : a ∈ Ω) (hDa : D a = 0)
    (hD : AnalyticOnNhd ℂ D Ω) (hfinite : ∀ z ∈ Ω, analyticOrderAt D z ≠ ⊤)
    (hH : AnalyticOnNhd ℂ H Ω) (hJ : AnalyticOnNhd ℂ J Ω)
    (heH : ∀ z ∈ Ω, D z*deriv H z+(deriv D z/2)*H z = g z)
    (heJ : ∀ z ∈ Ω, D z*deriv J z+(deriv D z/2)*J z = g z) :
    EqOn H J Ω := by
  have hzero := radicand_equation_homogeneous_eq_zero D (fun z => H z-J z) Ω a
    hΩ hconn ha hDa hD hfinite (hH.sub hJ) (by
      intro z hz
      have hd : HasDerivAt (fun w => H w-J w) (deriv H z-deriv J z) z :=
        (hH z hz).differentiableAt.hasDerivAt.sub (hJ z hz).differentiableAt.hasDerivAt
      rw [hd.deriv]
      linear_combination heH z hz-heJ z hz)
  exact fun z hz => sub_eq_zero.mp (hzero z hz)

theorem radicand_equation_divide_multiplier
    (Q K H : ℂ → ℂ) (z g : ℂ) (hQ : DifferentiableAt ℂ Q z)
    (hK : DifferentiableAt ℂ K z) (hH : DifferentiableAt ℂ H z) (hne : K z ≠ 0)
    (heq : Q z*deriv H z+(deriv Q z/2)*H z = g) :
    (K z^2*Q z)*deriv (fun w => H w/K w) z+
      (deriv (fun w => K w^2*Q w) z/2)*(H z/K z) = K z*g := by
  have hd := hH.hasDerivAt.fun_div hK.hasDerivAt hne
  have hp := (hK.hasDerivAt.pow 2).fun_mul hQ.hasDerivAt
  change HasDerivAt (fun w => K w^2*Q w) _ z at hp
  rw [hd.deriv,hp.deriv]
  simp only [Pi.pow_apply,Nat.cast_ofNat,show (2:ℕ)-1 = 1 from rfl,pow_one]
  field_simp [hne] at heq ⊢
  linear_combination K z*heq

end NLS.ComplexAnalysis
