import NLS.KdV.ClassicalHillLenardIdentity

/-! # Actual Dirichlet state boundary terms for Lenard directions

The constructed scalar Dirichlet state supplies a genuine concomitant.
Its boundary term is retained, including at band edges and closed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory MvPolynomial
open scoped ContDiff
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.DifferentialPolynomial
namespace NLS.KdV

theorem integral_classicalHillDirichletSquare_lenard
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (b : ℂ) (p : DifferentialPolynomial.Polynomial)
    (hz : (classicalHillFlow (scalarPotentialCurve f hf.continuous) b (0,1) 1).1=0) :
    (∫ x in (0:ℝ)..1, (classicalHillFlow (scalarPotentialCurve f hf.continuous) b (0,1) x).1^2*
      evaluate f 0 (hillLenardPolynomial b p) x)=
        -2*evaluate f 0 p 0*((classicalHillFlow (scalarPotentialCurve f hf.continuous) b (0,1) 1).2^2-1) := by
  let q := scalarPotentialCurve f hf.continuous
  let S := classicalHillFlow q b (0,1)
  let g := fun x => (S x).1^2
  let h := fun x => 2*(S x).1*(S x).2
  let j := fun x => (S x).2^2
  have hs (t : Icc (0:ℝ) 1) : HasDerivAt (fun x => (S x).1) (S t).2 t.val := by
    simpa [S] using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b (0,1) t).fst
  have hv (t : Icc (0:ℝ) 1) : HasDerivAt (fun x => (S x).2) ((q t-b)*(S t).1) t.val := by
    simpa [S] using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b (0,1) t).snd
  have hgD (t : Icc (0:ℝ) 1) : HasDerivAt g (h t) t.val := by
    convert! (hs t).pow 2 using 1
    dsimp [h]
    ring
  have hhD (t : Icc (0:ℝ) 1) : HasDerivAt h (2*j t+2*(q t-b)*g t) t.val := by
    convert! ((hs t).const_mul 2).mul (hv t) using 1
    dsimp [g,j]
    ring
  have hjD (t : Icc (0:ℝ) 1) : HasDerivAt j ((q t-b)*h t) t.val := by
    convert! (hv t).pow 2 using 1
    dsimp [h]
    ring
  have hcS : Continuous S := continuous_classicalHillFlow q b (0,1)
  have hcg : Continuous g := by dsimp [g];fun_prop
  have hch : Continuous h := by dsimp [h];fun_prop
  have hcj : Continuous j := by dsimp [j];fun_prop
  let a (n : ℕ) := evaluate f 0
    (((spatialDerivative : DifferentialPolynomial.Polynomial → DifferentialPolynomial.Polynomial)^[n]) p)
  have ha (n : ℕ) (x : ℝ) : HasDerivAt (a n) (a (n+1) x) x := by
    simpa only [a,Function.iterate_succ_apply'] using
      hasDerivAt_evaluate f 0 hf contDiff_const
        (((spatialDerivative : DifferentialPolynomial.Polynomial → DifferentialPolynomial.Polynomial)^[n]) p) x
  have hca (n : ℕ) : Continuous (a n) :=
    continuous_iff_continuousAt.mpr (fun x => (ha n x).continuousAt)
  let U (x : ℝ) : ℂ := -a 2 x*g x+a 1 x*h x-2*a 0 x*j x+2*a 0 x*(f x-b)*g x
  have hd (t : Icc (0:ℝ) 1) : HasDerivAt U
      (g t*evaluate f 0 (hillLenardPolynomial b p) t) t.val := by
    have hg := hgD t
    have hh := hhD t
    have hj := hjD t
    have hf0 : HasDerivAt f (iteratedDeriv 1 f t) t.val := by
      rw [iteratedDeriv_one]
      exact (hf.differentiable (by simp) t).hasDerivAt
    convert! (((((ha 2 t).neg.mul hg).add ((ha 1 t).mul hh)).sub
      (((ha 0 t).const_mul 2).mul hj)).add
        (((((ha 0 t).const_mul 2).mul (hf0.sub_const b))).mul hg)) using 1
    simp [q,scalarPotentialCurve,g,h,j,a,hillLenardPolynomial,evaluate]
    ring
  have hc : Continuous U := by
    have hg := hcg
    have hh := hch
    have hj := hcj
    have hc0 := hca 0
    have hc1 := hca 1
    have hc2 := hca 2
    dsimp only [U,g,h,j]
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ)≤1)
    hc.continuousOn (fun x (hx : x∈Ioo (0:ℝ) 1) => hd ⟨x,hx.1.le,hx.2.le⟩)
    ((hcg.mul
      (continuous_evaluate f 0 hf contDiff_const (hillLenardPolynomial b p))).intervalIntegrable 0 1)
  have he (n : ℕ) : a n 1=a n 0 := by
    simpa only [zero_add] using periodic_evaluate f 0 1 hp (fun _ => rfl)
      (((spatialDerivative : DifferentialPolynomial.Polynomial → DifferentialPolynomial.Polynomial)^[n]) p) 0
  have hU : U 1-U 0= -2*evaluate f 0 p 0*((S 1).2^2-1) := by
    have hzS : (S 1).1=0 := hz
    dsimp only [U,g,h,j]
    rw [hzS,show S 0=(0,1) from classicalHillFlow_zero q b (0,1),he 0]
    dsimp only [a]
    simp only [Function.iterate_zero,Function.id_def,zero_pow (by decide : 2≠0),mul_zero,zero_mul,add_zero]
    ring
  exact hi.trans hU


/-- The actual mixed-state pairing retains the endpoint slope term. -/
theorem integral_classicalHillDirichletMixed_lenard
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (b : ℂ) (p : DifferentialPolynomial.Polynomial)
    (hz : (classicalHillFlow (scalarPotentialCurve f hf.continuous) b (0,1) 1).1=0) :
    (∫ x in (0:ℝ)..1, (classicalHillFlow (scalarPotentialCurve f hf.continuous) b (1,0) x).1*
      (classicalHillFlow (scalarPotentialCurve f hf.continuous) b (0,1) x).1*
      evaluate f 0 (hillLenardPolynomial b p) x)=
        -2*evaluate f 0 p 0*(classicalHillFlow (scalarPotentialCurve f hf.continuous) b (1,0) 1).2*
          (classicalHillFlow (scalarPotentialCurve f hf.continuous) b (0,1) 1).2 := by
  let q := scalarPotentialCurve f hf.continuous
  let S := classicalHillFlow q b (0,1)
  let C := classicalHillFlow q b (1,0)
  let g := fun x => (C x).1*(S x).1
  let h := fun x => (C x).2*(S x).1+(C x).1*(S x).2
  let j := fun x => (C x).2*(S x).2
  have hs (t : Icc (0:ℝ) 1) : HasDerivAt (fun x => (S x).1) (S t).2 t.val := by
    simpa [S] using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b (0,1) t).fst
  have hv (t : Icc (0:ℝ) 1) : HasDerivAt (fun x => (S x).2) ((q t-b)*(S t).1) t.val := by
    simpa [S] using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b (0,1) t).snd
  have hc (t : Icc (0:ℝ) 1) : HasDerivAt (fun x => (C x).1) (C t).2 t.val := by
    simpa [C] using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b (1,0) t).fst
  have hw (t : Icc (0:ℝ) 1) : HasDerivAt (fun x => (C x).2) ((q t-b)*(C t).1) t.val := by
    simpa [C] using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b (1,0) t).snd
  have hgD (t : Icc (0:ℝ) 1) : HasDerivAt g (h t) t.val := by
    exact (hc t).mul (hs t)
  have hhD (t : Icc (0:ℝ) 1) : HasDerivAt h (2*j t+2*(q t-b)*g t) t.val := by
    convert! ((hw t).mul (hs t)).add ((hc t).mul (hv t)) using 1
    dsimp [g,j]
    ring
  have hjD (t : Icc (0:ℝ) 1) : HasDerivAt j ((q t-b)*h t) t.val := by
    convert! (hw t).mul (hv t) using 1
    dsimp [h]
    ring
  have hcS : Continuous S := continuous_classicalHillFlow q b (0,1)
  have hcC : Continuous C := continuous_classicalHillFlow q b (1,0)
  have hcg : Continuous g := by dsimp [g];fun_prop
  have hch : Continuous h := by dsimp [h];fun_prop
  have hcj : Continuous j := by dsimp [j];fun_prop
  let a (n : ℕ) := evaluate f 0
    (((spatialDerivative : DifferentialPolynomial.Polynomial → DifferentialPolynomial.Polynomial)^[n]) p)
  have ha (n : ℕ) (x : ℝ) : HasDerivAt (a n) (a (n+1) x) x := by
    simpa only [a,Function.iterate_succ_apply'] using
      hasDerivAt_evaluate f 0 hf contDiff_const
        (((spatialDerivative : DifferentialPolynomial.Polynomial → DifferentialPolynomial.Polynomial)^[n]) p) x
  have hca (n : ℕ) : Continuous (a n) :=
    continuous_iff_continuousAt.mpr (fun x => (ha n x).continuousAt)
  let U (x : ℝ) : ℂ := -a 2 x*g x+a 1 x*h x-2*a 0 x*j x+2*a 0 x*(f x-b)*g x
  have hd (t : Icc (0:ℝ) 1) : HasDerivAt U
      (g t*evaluate f 0 (hillLenardPolynomial b p) t) t.val := by
    have hg := hgD t
    have hh := hhD t
    have hj := hjD t
    have hf0 : HasDerivAt f (iteratedDeriv 1 f t) t.val := by
      rw [iteratedDeriv_one]
      exact (hf.differentiable (by simp) t).hasDerivAt
    convert! (((((ha 2 t).neg.mul hg).add ((ha 1 t).mul hh)).sub
      (((ha 0 t).const_mul 2).mul hj)).add
        (((((ha 0 t).const_mul 2).mul (hf0.sub_const b))).mul hg)) using 1
    simp [q,scalarPotentialCurve,g,h,j,a,hillLenardPolynomial,evaluate]
    ring
  have hc : Continuous U := by
    have hg := hcg
    have hh := hch
    have hj := hcj
    have hc0 := hca 0
    have hc1 := hca 1
    have hc2 := hca 2
    dsimp only [U,g,h,j]
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ)≤1)
    hc.continuousOn (fun x (hx : x∈Ioo (0:ℝ) 1) => hd ⟨x,hx.1.le,hx.2.le⟩)
    ((hcg.mul
      (continuous_evaluate f 0 hf contDiff_const (hillLenardPolynomial b p))).intervalIntegrable 0 1)
  have he (n : ℕ) : a n 1=a n 0 := by
    simpa only [zero_add] using periodic_evaluate f 0 1 hp (fun _ => rfl)
      (((spatialDerivative : DifferentialPolynomial.Polynomial → DifferentialPolynomial.Polynomial)^[n]) p) 0
  have hU : U 1-U 0= -2*evaluate f 0 p 0*(C 1).2*(S 1).2 := by
    have hzS : (S 1).1=0 := hz
    have hdet := classicalHillFlow_endpoint_det q b
    change (C 1).1*(S 1).2-(C 1).2*(S 1).1=1 at hdet
    rw [hzS,mul_zero,sub_zero] at hdet
    dsimp only [U,g,h,j]
    rw [hzS,show S 0=(0,1) from classicalHillFlow_zero q b (0,1),
      show C 0=(1,0) from classicalHillFlow_zero q b (1,0),he 0,he 1,hdet]
    dsimp only [a]
    simp only [Function.iterate_zero,Function.id_def,mul_zero,mul_one,add_zero,zero_add]
    ring
  exact hi.trans hU

end NLS.KdV
