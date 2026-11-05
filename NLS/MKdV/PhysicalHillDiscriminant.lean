import NLS.MKdV.QuasiHillPhysicalUniqueness

/-! # The physical Miura–Hill initial-value problem and its discriminant

The scalar columns have the original initial conditions (g(0),g'(0))=(1,0)
and (0,1). Their physical equation and uniqueness follow from proved statements
about the independent Volterra construction. The discriminant is the literal
sum of their physical endpoint diagonal entries.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.MKdV
local notation "t₀" => (⟨0,by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)
local notation "t₁" => (⟨1,by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)

/-- Independent scalar Hill solution with prescribed position and derivative. -/
def physicalMiuraSolution (U : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ) : ℝ → ℂ :=
  fun x => (quasiHillSolution U μ (v.1,v.2-U t₀*v.1) x).1

@[simp] theorem physicalMiuraSolution_zero (U : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ) :
    physicalMiuraSolution U μ v 0 = v.1 := by
  simp only [physicalMiuraSolution, quasiHillSolution_zero]

theorem deriv_physicalMiuraSolution (U : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    deriv (physicalMiuraSolution U μ v) t =
      U t*(quasiHillSolution U μ (v.1,v.2-U t₀*v.1) t).1+
        (quasiHillSolution U μ (v.1,v.2-U t₀*v.1) t).2 :=
  (hasDerivAt_fst_quasiHillSolution U μ (v.1,v.2-U t₀*v.1) t).deriv

@[simp] theorem deriv_physicalMiuraSolution_zero (U : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ) :
    deriv (physicalMiuraSolution U μ v) 0 = v.2 := by
  have h := deriv_physicalMiuraSolution U μ v t₀
  simp only [quasiHillSolution_zero] at h
  calc
    deriv (physicalMiuraSolution U μ v) 0 = U t₀*v.1+(v.2-U t₀*v.1) := h
    _ = v.2 := by ring

/-- The actual scalar IVP has absolute continuity and the physical equation
on the full absolutely continuous potential domain. -/
theorem physicalMiuraSolution_spec (U : Curve ℂ) (u : ℝ → ℂ)
    (hU : ∀ t, U t = u t) (hu : AbsolutelyContinuousOnInterval u 0 1)
    (μ : ℂ) (v : ℂ × ℂ) :
    AbsolutelyContinuousOnInterval (physicalMiuraSolution U μ v) 0 1 ∧
      AbsolutelyContinuousOnInterval (deriv (physicalMiuraSolution U μ v)) 0 1 ∧
      ∀ᵐ x : ℝ, x ∈ Ioo (0 : ℝ) 1 →
        -deriv (deriv (physicalMiuraSolution U μ v)) x+
          miuraPotential u x*physicalMiuraSolution U μ v x =
            μ*physicalMiuraSolution U μ v x := by
  have hr := quasiHillSolution_scalar_regular U u hU hu μ (v.1,v.2-U t₀*v.1)
  exact ⟨hr.1,hr.2,quasiHillSolution_scalar_equation_ae U u hU hu μ (v.1,v.2-U t₀*v.1)⟩

/-- The physical differential equation and initial position/derivative uniquely
determine the independently constructed scalar column. -/
theorem physicalMiuraSolution_unique (U : Curve ℂ) (u : ℝ → ℂ)
    (hU : ∀ t, U t = u t) (hu : AbsolutelyContinuousOnInterval u 0 1)
    (μ : ℂ) (v : ℂ × ℂ) (g : ℝ → ℂ)
    (hg : AbsolutelyContinuousOnInterval g 0 1)
    (hdg : AbsolutelyContinuousOnInterval (deriv g) 0 1)
    (heq : ∀ᵐ x : ℝ, x ∈ Ioo (0 : ℝ) 1 →
      -deriv (deriv g) x+miuraPotential u x*g x = μ*g x)
    (h0 : g 0 = v.1) (hd0 : deriv g 0 = v.2) :
    EqOn g (physicalMiuraSolution U μ v) (Icc 0 1) := by
  have h := physicalMiuraSolution_eq_quasiHill U u hU hu μ g hg hdg heq
  intro x hx
  have he := congrArg Prod.fst (h hx)
  rw [h0,hd0,← hU t₀] at he
  exact he

/-- The literal discriminant in position/derivative normalization. -/
def physicalMiuraDiscriminant (U : Curve ℂ) (μ : ℂ) : ℂ :=
  physicalMiuraSolution U μ (1,0) 1+deriv (physicalMiuraSolution U μ (0,1)) 1

/-- Matching endpoint values of u make the physical and quasi-derivative
normalizations conjugate, hence their literal traces coincide. -/
theorem physicalMiuraDiscriminant_eq_quasiHill (U : Curve ℂ) (hU : U t₁ = U t₀) (μ : ℂ) :
    physicalMiuraDiscriminant U μ = quasiHillDiscriminant U μ := by
  let M := solutionMap (quasiHillCoefficientCurve U μ) t₁
  have hMa (v : ℂ × ℂ) : quasiHillSolution U μ v 1 = M v :=
    (solutionMap_apply (quasiHillCoefficientCurve U μ) t₁ v).symm
  have he : ((1 : ℂ), -(U t₀)) = ((1 : ℂ),0)-(U t₀) • ((0 : ℂ),1) := by simp
  have hM : M ((1 : ℂ),-(U t₀)) = M (1,0)-(U t₀) • M (0,1) := by
    rw [he,map_sub,map_smul]
  rw [physicalMiuraDiscriminant, deriv_physicalMiuraSolution U μ (0,1) t₁]
  simp only [physicalMiuraSolution, mul_one, zero_sub, mul_zero, sub_zero]
  simp_rw [hMa]
  change (M (1,-U t₀)).1+(U t₁*(M (0,1)).1+(M (0,1)).2) = _
  rw [hM,hU]
  rw [quasiHillDiscriminant,trace_pairCLM]
  change (M (1,0)).1-U t₀*(M (0,1)).1+(U t₀*(M (0,1)).1+(M (0,1)).2) =
    (M (1,0)).1+(M (0,1)).2
  ring

end NLS.MKdV
