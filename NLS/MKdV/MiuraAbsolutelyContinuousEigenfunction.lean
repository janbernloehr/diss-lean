import NLS.MKdV.MiuraClassicalSolution
import NLS.FunctionalAnalysis.LinearVolterraRegularity

/-! # Miura intertwining for arbitrary physical eigenfunctions

The input is an arbitrary componentwise absolutely continuous function
satisfying the literal physical first-order eigen-equation almost everywhere.
It is not assumed to be a constructed initial-value solution. Continuous
coefficients and AC uniqueness supply that identification. Thus the scalar
factorization holds in a class containing the paper's interval H2 functions.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory NLS.LinearVolterra
open NLS.FunctionalAnalysis NLS.ZakharovShabat
namespace NLS.MKdV

/-- The literal vector second-derivative identity in Lemma 2's proof. -/
theorem hasDerivAt_deriv_classicalSolution_diagonal
    (Φ : Curve (ℂ × ℂ)) (u : ℝ → ℂ) (z : ℂ) (v : ℂ × ℂ)
    (hΦ : ∀ t : Icc (0:ℝ) 1, Φ t = (u t,u t))
    (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) (hu : DifferentiableAt ℝ u x) :
    HasDerivAt (deriv (classicalSolution Φ z v))
      (I*deriv u x*(classicalSolution Φ z v x).2+
        (-z^2+(u x)^2)*(classicalSolution Φ z v x).1,
       -I*deriv u x*(classicalSolution Φ z v x).1+
        (-z^2+(u x)^2)*(classicalSolution Φ z v x).2) x := by
  have hf := hasDerivAt_classicalSolution Φ z v ⟨x,hx.1.le,hx.2.le⟩
  rw [hΦ ⟨x,hx.1.le,hx.2.le⟩] at hf
  have hf₁ := HasFDerivAt.hasDerivAt hf.fst
  have hf₂ := HasFDerivAt.hasDerivAt hf.snd
  have hsecond := ((hf₁.const_mul (-I*z)).add ((hu.hasDerivAt.mul hf₂).const_mul I)).prodMk
    (((hu.hasDerivAt.mul hf₁).const_mul (-I)).add (hf₂.const_mul (I*z)))
  have hn : deriv (classicalSolution Φ z v) =ᶠ[𝓝 x]
      (fun y => (-I*z*(classicalSolution Φ z v y).1+I*u y*(classicalSolution Φ z v y).2,
        -I*u y*(classicalSolution Φ z v y).1+I*z*(classicalSolution Φ z v y).2)) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    have hd := (hasDerivAt_classicalSolution Φ z v ⟨y,hy.1.le,hy.2.le⟩).deriv
    rw [hΦ ⟨y,hy.1.le,hy.2.le⟩] at hd
    exact hd
  have hd := hsecond.congr_of_eventuallyEq (by
    simpa only [Pi.add_apply,Pi.mul_apply,mul_assoc] using hn)
  convert! hd using 1
  apply Prod.ext <;>
    simp only [classicalODECoefficient_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply,one_smul] <;> dsimp <;> ring_nf <;> simp [I_sq]
  all_goals ring

/-- The actual transformed columns have exactly the displayed physical
position/derivative transfer entries. -/
theorem deriv_classicalMiuraSolution_entries
    (Φ : Curve (ℂ × ℂ)) (u : ℝ → ℂ) (z : ℂ) (v : ℂ × ℂ)
    (hΦ : ∀ t : Icc (0:ℝ) 1, Φ t = (u t,u t)) (t : Icc (0:ℝ) 1) :
    deriv (classicalMiuraSolution Φ z v) t =
      (u t-I*z)*(classicalSolution Φ z v t).1+
        (I*u t-z)*(classicalSolution Φ z v t).2 := by
  rw [(hasDerivAt_classicalMiuraSolution Φ u z v hΦ t).deriv]
  dsimp [classicalMiuraSolution,classicalMiuraPartner]
  ring_nf
  simp only [I_sq]
  ring

/-- Arbitrary AC physical eigenfunctions equal the actual normalized IVP
solution with their initial vector, throughout the closed interval. -/
theorem classicalSolution_eq_of_ac_physical_eigenfunction
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (f : ℝ → ℂ × ℂ)
    (hf₁ : AbsolutelyContinuousOnInterval (fun x => (f x).1) 0 1)
    (hf₂ : AbsolutelyContinuousOnInterval (fun x => (f x).2) 0 1)
    (he : ∀ᵐ x : ℝ, x ∈ Icc (0:ℝ) 1 →
      physicalOperator (extend Φ) f x = z • f x) :
    EqOn f (classicalSolution Φ z (f 0)) (Icc 0 1) := by
  have ha := absolutelyContinuousOnInterval_clm hf₁ (ContinuousLinearMap.inl ℝ ℂ ℂ)
  have hb := absolutelyContinuousOnInterval_clm hf₂ (ContinuousLinearMap.inr ℝ ℂ ℂ)
  have hf : AbsolutelyContinuousOnInterval f 0 1 := by
    apply absolutelyContinuousOnInterval_congr (ha.add hb)
    intro x _
    simp only [Pi.add_apply,ContinuousLinearMap.inl_apply,ContinuousLinearMap.inr_apply,
      Prod.add_def,add_zero,zero_add,Prod.mk.eta]
  apply solution_unique_of_ac (classicalODECurve Φ z) f hf
  filter_upwards [ae_differentiableAt_complex hf₁,ae_differentiableAt_complex hf₂,he]
    with x hx₁ hx₂ hxe
  intro hx
  have hxi : x ∈ uIcc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx
  have hd := (hx₁ hxi).hasDerivAt.prodMk (hx₂ hxi).hasDerivAt
  have h := hxe hx
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  rw [extend_coe _ ⟨x,hx⟩]
  convert! hd using 1
  apply Prod.ext
  · change -I*z*(f x).1+I*(Φ ⟨x,hx⟩).1*(f x).2 = deriv (fun y => (f y).1) x
    change I*deriv (fun y => (f y).1) x+(extend Φ x).1*(f x).2 = z*(f x).1 at h₁
    rw [extend_coe _ ⟨x,hx⟩] at h₁
    linear_combination (norm := (ring_nf; simp [I_sq])) I*h₁
  · change -I*(Φ ⟨x,hx⟩).2*(f x).1+I*z*(f x).2 = deriv (fun y => (f y).2) x
    change -I*deriv (fun y => (f y).2) x+(extend Φ x).2*(f x).1 = z*(f x).2 at h₂
    rw [extend_coe _ ⟨x,hx⟩] at h₂
    linear_combination (norm := (ring_nf; simp [I_sq])) -I*h₂

/-- The proof's vector identity also holds for an arbitrary AC physical
eigenfunction, independently of how it was originally presented. -/
theorem hasDerivAt_deriv_of_ac_physical_eigenfunction
    (Φ : Curve (ℂ × ℂ)) (u : ℝ → ℂ) (z : ℂ) (f : ℝ → ℂ × ℂ)
    (hΦ : ∀ t : Icc (0:ℝ) 1, Φ t = (u t,u t))
    (hf₁ : AbsolutelyContinuousOnInterval (fun x => (f x).1) 0 1)
    (hf₂ : AbsolutelyContinuousOnInterval (fun x => (f x).2) 0 1)
    (he : ∀ᵐ x : ℝ, x ∈ Icc (0:ℝ) 1 →
      physicalOperator (extend Φ) f x = z • f x)
    (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) (hu : DifferentiableAt ℝ u x) :
    HasDerivAt (deriv f)
      (I*deriv u x*(f x).2+(-z^2+(u x)^2)*(f x).1,
       -I*deriv u x*(f x).1+(-z^2+(u x)^2)*(f x).2) x := by
  have heq := classicalSolution_eq_of_ac_physical_eigenfunction Φ z f hf₁ hf₂ he
  have hn : f =ᶠ[𝓝 x] classicalSolution Φ z (f 0) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact heq ⟨hy.1.le,hy.2.le⟩
  have hd := hasDerivAt_deriv_classicalSolution_diagonal Φ u z (f 0) hΦ x hx hu
  rw [← hn.eq_of_nhds] at hd
  exact hd.congr_of_eventuallyEq hn.deriv

/-- The scalar physical equation holds for every arbitrary AC eigenfunction
at each interior point where the potential is differentiable. -/
theorem miura_equation_of_ac_physical_eigenfunction
    (Φ : Curve (ℂ × ℂ)) (u : ℝ → ℂ) (z : ℂ) (f : ℝ → ℂ × ℂ)
    (hΦ : ∀ t : Icc (0:ℝ) 1, Φ t = (u t,u t))
    (hf₁ : AbsolutelyContinuousOnInterval (fun x => (f x).1) 0 1)
    (hf₂ : AbsolutelyContinuousOnInterval (fun x => (f x).2) 0 1)
    (he : ∀ᵐ x : ℝ, x ∈ Icc (0:ℝ) 1 →
      physicalOperator (extend Φ) f x = z • f x)
    (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) (hu : DifferentiableAt ℝ u x) :
    let g := fun y => (f y).1+I*(f y).2;
    -deriv (deriv g) x+miuraPotential u x*g x = z^2*g x := by
  have heq := classicalSolution_eq_of_ac_physical_eigenfunction Φ z f hf₁ hf₂ he
  have hn : (fun y => (f y).1+I*(f y).2) =ᶠ[𝓝 x] classicalMiuraSolution Φ z (f 0) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    dsimp [classicalMiuraSolution]
    rw [heq ⟨hy.1.le,hy.2.le⟩]
  change -deriv (deriv (fun y => (f y).1+I*(f y).2)) x+
    miuraPotential u x*((f x).1+I*(f x).2) = z^2*((f x).1+I*(f x).2)
  rw [hn.deriv.deriv_eq,hn.eq_of_nhds]
  exact miura_equation_classicalSolution Φ u z (f 0) hΦ x hx hu

end NLS.MKdV
