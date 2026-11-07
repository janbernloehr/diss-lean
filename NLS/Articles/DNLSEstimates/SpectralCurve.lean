import NLS.Articles.DNLSEstimates.ComplexFiniteGap
import NLS.ComplexAnalysis.PrescribedAnalyticSquareRoot
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Analytic.Order

/-!
# Local analytic geometry of the actual spectral curve

The affine curve lies in `ℂ × ℂ`. Its local equations distinguish
unramified points, simple branch points, and double spectral points.
These are actual analytic uniformizers and two-branch equations; this
module does not identify the genus of the resulting global surface.
-/
noncomputable section
open Set Complex Metric Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.Articles.DNLSEstimates

/-- The actual two-sheeted affine curve over a radicand. -/
def doubleCover (f : ℂ → ℂ) : Set (ℂ × ℂ) := {q | q.2 ^ 2 = f q.1}

/-- The paper's curve, with its actual source discriminant. -/
def spectralCurve {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (a : CoeffPair p) :
    Set (ℂ × ℂ) := doubleCover (fun z => (canonicalDiscriminant hp (periodOnePotential a) z)^2-4)

/-- Off the branch locus the curve is exactly one analytic graph near
each of its two points; the normalization is prescribed by that point. -/
theorem doubleCover_unramified_graph (f : ℂ → ℂ) (z w : ℂ)
    (hf : AnalyticAt ℂ f z) (hw : w ≠ 0) (hbase : w^2 = f z) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h z ∧ h z = w ∧
      (∀ x : ℂ, (x,h x) ∈ doubleCover f) ∧
      ∀ᶠ q : ℂ × ℂ in 𝓝 (z,w), q ∈ doubleCover f ↔ q.2 = h q.1 := by
  let h := prescribedSquareRoot f w
  have hrad : AnalyticAt ℂ (fun x => f x/w^2) z :=
    hf.div analyticAt_const (pow_ne_zero 2 hw)
  have hnorm : f z/w^2 = 1 := by rw [← hbase,div_self (pow_ne_zero 2 hw)]
  have hsqrt : AnalyticAt ℂ Complex.sqrt (f z/w^2) := by
    rw [hnorm]
    exact Complex.differentiableOn_sqrt.analyticAt
      (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)
  have hh : AnalyticAt ℂ h z := by
    have hc := hsqrt.comp (f := fun x => f x/w^2) hrad
    exact analyticAt_const.mul hc
  have hhz : h z = w := prescribedSquareRoot_base f w hw z hbase.symm
  have hsq (x : ℂ) : h x ^ 2 = f x := prescribedSquareRoot_sq f w hw x
  refine ⟨h,hh,hhz,fun x => hsq x,?_⟩
  have hc1 : ContinuousAt (fun q : ℂ × ℂ => h q.1) (z,w) :=
    hh.continuousAt.comp (f := fun q : ℂ × ℂ => q.1) (x := (z,w)) continuousAt_fst
  have hc : ContinuousAt (fun q : ℂ × ℂ => q.2 + h q.1) (z,w) :=
    continuousAt_snd.fun_add hc1
  have hne : w+h z ≠ 0 := by rw [hhz,← two_mul]; exact mul_ne_zero (by norm_num) hw
  filter_upwards [hc.eventually_ne hne] with q hq
  change q.2^2 = f q.1 ↔ q.2 = h q.1
  rw [← hsq q.1]
  constructor
  · intro hqroot
    rcases eq_or_eq_neg_of_sq_eq_sq q.2 (h q.1) hqroot with he | he
    · exact he
    · exact (hq (by rw [he]; ring)).elim
  · intro he
    rw [he]

/-- A simple zero gives the ramified analytic coordinate `w`, with
projection `w ↦ f⁻¹(w²)`. Both directions of the local equation are proved. -/
theorem doubleCover_simple_uniformizer (f : ℂ → ℂ) (z : ℂ)
    (hf : AnalyticAt ℂ f z) (hz : f z = 0) (hd : deriv f z ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = z ∧
      (∀ᶠ w : ℂ in 𝓝 0, (g (w^2),w) ∈ doubleCover f) ∧
      ∀ᶠ q : ℂ × ℂ in 𝓝 (z,0), q ∈ doubleCover f ↔ q.1 = g (q.2^2) := by
  let g := hf.hasStrictDerivAt.localInverse f (deriv f z) z hd
  have hg : AnalyticAt ℂ g 0 := by simpa only [hz] using hf.analyticAt_localInverse hd
  have hg0 : g 0 = z := by
    rw [← hz]
    exact HasStrictFDerivAt.localInverse_apply_image ..
  have hl : ∀ᶠ x in 𝓝 z, g (f x) = x := HasStrictDerivAt.eventually_left_inverse ..
  have hr : ∀ᶠ y in 𝓝 (0 : ℂ), f (g y) = y := by
    simpa only [hz] using (show ∀ᶠ y in 𝓝 (f z), f (g y) = y from
      HasStrictDerivAt.eventually_right_inverse ..)
  have hsq : Tendsto (fun w : ℂ => w^2) (𝓝 0) (𝓝 0) := by
    simpa using (continuousAt_id.fun_pow 2).tendsto (x := (0 : ℂ))
  refine ⟨g,hg,hg0,?_,?_⟩
  · filter_upwards [hsq.eventually hr] with w hw
    exact hw.symm
  · have hfst : Tendsto (fun q : ℂ × ℂ => q.1) (𝓝 (z,0)) (𝓝 z) := continuousAt_fst.tendsto
    have hsnd : Tendsto (fun q : ℂ × ℂ => q.2^2) (𝓝 (z,0)) (𝓝 (0 : ℂ)) := by
      simpa using
        (continuousAt_snd.fun_pow 2).tendsto (x := (z,(0 : ℂ)))
    filter_upwards [hfst.eventually hl,hsnd.eventually hr] with q hleft hright
    change q.2^2 = f q.1 ↔ q.1 = g (q.2^2)
    constructor
    · intro he
      rw [he,hleft]
    · intro he
      rw [he,hright]

/-- A double zero has two analytic branches with distinct tangent slopes.
This is the local normalization at a double periodic spectral point. -/
theorem doubleCover_double_branches (f : ℂ → ℂ) (z : ℂ)
    (hf : AnalyticAt ℂ f z) (ho : analyticOrderAt f z = 2) :
    ∃ b : ℂ → ℂ, AnalyticAt ℂ b z ∧ b z = 0 ∧ deriv b z ≠ 0 ∧
      deriv b z ≠ deriv (fun x => -b x) z ∧
      ∀ᶠ x : ℂ in 𝓝 z, ∀ w : ℂ,
        (x,w) ∈ doubleCover f ↔ w = b x ∨ w = -b x := by
  obtain ⟨g,hg,hg0,he⟩ := hf.analyticOrderAt_eq_natCast.mp ho
  let v := Complex.sqrt (g z)
  have hv : v^2 = g z := by
    have he := Complex.cpow_nat_inv_pow (g z) (by decide : 2 ≠ 0)
    norm_num at he
    simpa only [v,Complex.sqrt,one_div] using he
  have hv0 : v ≠ 0 := by
    intro hzero
    exact hg0 (by rw [← hv,hzero]; ring)
  let h := prescribedSquareRoot g v
  have hrad : AnalyticAt ℂ (fun x => g x/v^2) z := hg.div analyticAt_const (pow_ne_zero 2 hv0)
  have hnorm : g z/v^2 = 1 := by rw [← hv,div_self (pow_ne_zero 2 hv0)]
  have hsqrt : AnalyticAt ℂ Complex.sqrt (g z/v^2) := by
    rw [hnorm]
    exact Complex.differentiableOn_sqrt.analyticAt
      (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)
  have hh : AnalyticAt ℂ h z := by
    have hc := hsqrt.comp (f := fun x => g x/v^2) hrad
    exact analyticAt_const.mul hc
  have hhz : h z = v := prescribedSquareRoot_base g v hv0 z hv.symm
  let b : ℂ → ℂ := fun x => (x-z)*h x
  have hb : AnalyticAt ℂ b z := (analyticAt_id.sub analyticAt_const).mul hh
  have hbd : deriv b z = v := by
    simpa only [b,id_eq,one_mul,sub_self,zero_mul,add_zero,hhz] using
      ((hasDerivAt_id z).sub_const z |>.fun_mul hh.differentiableAt.hasDerivAt).deriv
  refine ⟨b,hb,by simp [b],hbd ▸ hv0,?_,?_⟩
  · rw [hb.differentiableAt.hasDerivAt.fun_neg.deriv, hbd]
    intro hneg
    exact hv0 (by linear_combination (1/2 : ℂ)*hneg)
  · filter_upwards [he] with x hx w
    have hx' : f x = b x ^ 2 := by
      rw [hx]
      change (x-z)^2*g x = ((x-z)*h x)^2
      rw [mul_pow,prescribedSquareRoot_sq g v hv0 x]
    change w^2 = f x ↔ w = b x ∨ w = -b x
    rw [hx']
    exact sq_eq_sq_iff_eq_or_eq_neg

/-- Spectral invariance of the affine curve uses the actual discriminant,
not merely equality of a finite list of band endpoints. -/
theorem spectralCurve_eq_of_discriminant {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (a b : CoeffPair p)
    (h : canonicalDiscriminant hp (periodOnePotential a) =
      canonicalDiscriminant hp (periodOnePotential b)) :
    spectralCurve hp a = spectralCurve hp b := by unfold spectralCurve; rw [h]



/-- The actual ambient differential of the curve equation. -/
theorem doubleCover_defining_hasFDerivAt (f : ℂ → ℂ) (q : ℂ × ℂ)
    (hf : AnalyticAt ℂ f q.1) :
    HasFDerivAt (fun u : ℂ × ℂ => u.2^2-f u.1)
      ((2*q.2) • ContinuousLinearMap.snd ℂ ℂ ℂ -
        (deriv f q.1) • ContinuousLinearMap.fst ℂ ℂ ℂ) q := by
  have hs := (hasFDerivAt_snd (𝕜 := ℂ) (p := q)).pow 2
  have ht := hf.differentiableAt.hasDerivAt.hasFDerivAt.comp q (hasFDerivAt_fst (𝕜 := ℂ) (p := q))
  apply (hs.fun_sub ht).congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  change (2 • q.2^(2-1))*v.2-v.1*(deriv f q.1) = (2*q.2)*v.2-(deriv f q.1)*v.1
  norm_num [two_smul]
  ring

/-- Jacobian vanishing is exactly the simultaneous vanishing of the two
partial derivatives. This definition is independent of endpoint labels. -/
theorem doubleCover_differential_zero_iff (f : ℂ → ℂ) (q : ℂ × ℂ)
    (hf : AnalyticAt ℂ f q.1) :
    fderiv ℂ (fun u : ℂ × ℂ => u.2^2-f u.1) q = 0 ↔ q.2 = 0 ∧ deriv f q.1 = 0 := by
  rw [(doubleCover_defining_hasFDerivAt f q hf).fderiv]
  constructor
  · intro he
    have h1 := congrArg (fun L : (ℂ × ℂ) →L[ℂ] ℂ => L (1,0)) he
    have h2 := congrArg (fun L : (ℂ × ℂ) →L[ℂ] ℂ => L (0,1)) he
    change 2*q.2*0-deriv f q.1*1 = 0 at h1
    change 2*q.2*1-deriv f q.1*0 = 0 at h2
    simp only [mul_zero,mul_one,zero_sub,neg_eq_zero] at h1
    simp only [mul_zero,mul_one,sub_zero] at h2
    exact ⟨(mul_eq_zero.mp h2).resolve_left (by norm_num),h1⟩
  · rintro ⟨hw,hd⟩
    apply ContinuousLinearMap.ext
    intro v
    change 2*q.2*v.2-deriv f q.1*v.1 = 0
    rw [hw,hd]
    ring

/-- Regularity refers to the genuine ambient Jacobian of the equation. -/
def doubleCoverRegular (f : ℂ → ℂ) (q : ℂ × ℂ) : Prop :=
  fderiv ℂ (fun u : ℂ × ℂ => u.2^2-f u.1) q ≠ 0

/-- At a ramification point, regularity is equivalent to a simple zero. -/
theorem doubleCover_regular_branch_iff_simple (f : ℂ → ℂ) (z : ℂ)
    (hf : AnalyticAt ℂ f z) (hz : f z = 0) :
    doubleCoverRegular f (z,0) ↔ analyticOrderAt f z = 1 := by
  have ho : analyticOrderAt f z = 1 ↔ deriv f z ≠ 0 := by
    simpa only [Nat.cast_zero,zero_add] using
      (analyticOrderAt_deriv_eq_iff hf hz (n := 0)).trans hf.deriv.analyticOrderAt_eq_zero
  rw [ho]
  unfold doubleCoverRegular
  simp only [ne_eq]
  rw [doubleCover_differential_zero_iff f (z,0) hf]
  simp

/-- For the actual discriminant, nonsingularity at every curve point is
exactly simplicity of the entire periodic spectrum, including central roots. -/
theorem spectralCurve_regular_iff_simple {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : CoeffPair p) :
    (∀ q ∈ spectralCurve hp a,
      doubleCoverRegular (fun z => (canonicalDiscriminant hp (periodOnePotential a) z)^2-4) q) ↔
    ∀ z ∈ periodicSpectrum hp (periodOnePotential a),
      periodicAlgebraicMultiplicity hp (periodOnePotential a) z = 1 := by
  let f : ℂ → ℂ := fun z => (canonicalDiscriminant hp (periodOnePotential a) z)^2-4
  have hf (z : ℂ) : AnalyticAt ℂ f z :=
    ((analyticOnNhd_canonicalDiscriminant hp hp1 _ (periodOnePotential_mem a) z (mem_univ _)).pow 2).sub analyticAt_const
  have hzero (z : ℂ) : f z = 0 ↔ z ∈ periodicSpectrum hp (periodOnePotential a) := by
    exact sub_eq_zero.trans (canonicalDiscriminant_sq_eq_four_iff_finite hp hp1 _ (periodOnePotential_mem a) z)
  have horder (z : ℂ) : analyticOrderAt f z =
      (periodicAlgebraicMultiplicity hp (periodOnePotential a) z : ℕ∞) :=
    analyticOrderAt_canonicalDiscriminant_sq_sub_four hp hp1 _ (periodOnePotential_mem a) z
  constructor
  · intro h z hz
    have hq : (z,0) ∈ spectralCurve hp a := by
      change (0 : ℂ)^2 = f z
      rw [(hzero z).mpr hz]
      norm_num
    have ho := (doubleCover_regular_branch_iff_simple f z (hf z) ((hzero z).mpr hz)).mp (h _ hq)
    rw [horder] at ho
    exact_mod_cast ho
  · intro h q hq
    by_cases hw : q.2 = 0
    · have hz : f q.1 = 0 := by
        change q.2^2 = f q.1 at hq
        rw [hw] at hq
        simpa using hq.symm
      have ho : analyticOrderAt f q.1 = 1 := by rw [horder,h q.1 ((hzero q.1).mp hz)]; rfl
      have hr := (doubleCover_regular_branch_iff_simple f q.1 (hf q.1) hz).mpr ho
      simpa only [← hw] using hr
    · exact fun hn => hw ((doubleCover_differential_zero_iff f q (hf q.1)).mp hn).1

/-- Actual double spectral points have the two local branches above,
with distinct tangent directions; they are not treated as simple points. -/
theorem spectralCurve_double_point {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : CoeffPair p) (z : ℂ)
    (hm : periodicAlgebraicMultiplicity hp (periodOnePotential a) z = 2) :
    ∃ b : ℂ → ℂ, AnalyticAt ℂ b z ∧ b z = 0 ∧ deriv b z ≠ 0 ∧
      deriv b z ≠ deriv (fun x => -b x) z ∧
      ∀ᶠ x : ℂ in 𝓝 z, ∀ w : ℂ,
        (x,w) ∈ spectralCurve hp a ↔ w = b x ∨ w = -b x := by
  apply doubleCover_double_branches
  · exact ((analyticOnNhd_canonicalDiscriminant hp hp1 _ (periodOnePotential_mem a) z (mem_univ _)).pow 2).sub analyticAt_const
  · rw [analyticOrderAt_canonicalDiscriminant_sq_sub_four hp hp1 _ (periodOnePotential_mem a),hm]
    rfl



/-- The actual source has infinitely many periodic spectral points: its
canonical left endpoint norms escape to infinity. -/
theorem spectralCurve_infinite_periodic_spectrum {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : CoeffPair p) :
    (periodicSpectrum hp (periodOnePotential a)).Infinite := by
  intro hfin
  obtain ⟨B,hB⟩ := hfin.isCompact.isBounded.exists_norm_le
  obtain ⟨n,hn⟩ := ((tendsto_sourcePeriodicLeft_norm_atTop hp hp1 a).eventually
    (eventually_gt_atTop B)).exists
  exact (not_lt_of_ge (hB _ (canonicalPeriodicEndpoints_mem_spectrum hp hp1
    (periodOnePotential a) (periodOnePotential_mem a) n).1)) hn

/-- Every simple periodic point has a genuine ramified analytic uniformizer. -/
theorem spectralCurve_simple_point {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : CoeffPair p) (z : ℂ)
    (hm : periodicAlgebraicMultiplicity hp (periodOnePotential a) z = 1) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = z ∧
      (∀ᶠ w : ℂ in 𝓝 0, (g (w^2),w) ∈ spectralCurve hp a) ∧
      ∀ᶠ q : ℂ × ℂ in 𝓝 (z,0), q ∈ spectralCurve hp a ↔ q.1 = g (q.2^2) := by
  let f : ℂ → ℂ := fun x => (canonicalDiscriminant hp (periodOnePotential a) x)^2-4
  have hf : AnalyticAt ℂ f z :=
    ((analyticOnNhd_canonicalDiscriminant hp hp1 _ (periodOnePotential_mem a) z (mem_univ _)).pow 2).sub analyticAt_const
  have ho : analyticOrderAt f z = 1 := by
    rw [analyticOrderAt_canonicalDiscriminant_sq_sub_four hp hp1 _ (periodOnePotential_mem a),hm]
    rfl
  have hz : f z = 0 := hf.analyticOrderAt_ne_zero.mp (by rw [ho]; norm_num)
  have hd : deriv f z ≠ 0 := hf.deriv.analyticOrderAt_eq_zero.mp (by
    simpa only [Nat.cast_zero,zero_add] using (analyticOrderAt_deriv_eq_iff hf hz (n := 0)).mp ho)
  exact doubleCover_simple_uniformizer f z hf hz hd

/-- When the whole periodic spectrum is simple, the curve has infinitely
many distinct regular branch points. This is a ramification theorem;
it does not substitute a branch count for the separate genus assertion. -/
theorem spectralCurve_infinite_regular_branch_points {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : CoeffPair p)
    (hsimple : ∀ z ∈ periodicSpectrum hp (periodOnePotential a),
      periodicAlgebraicMultiplicity hp (periodOnePotential a) z = 1) :
    {q : ℂ × ℂ | q ∈ spectralCurve hp a ∧ q.2 = 0 ∧
      doubleCoverRegular (fun z => (canonicalDiscriminant hp (periodOnePotential a) z)^2-4) q}.Infinite := by
  have hi := (spectralCurve_infinite_periodic_spectrum hp hp1 a).image
    (f := fun z : ℂ => (z,(0 : ℂ))) (by intro x hx y hy h; exact congrArg Prod.fst h)
  apply hi.mono
  rintro _ ⟨z,hz,rfl⟩
  have hq : (z,0) ∈ spectralCurve hp a := by
    change (0 : ℂ)^2 = (canonicalDiscriminant hp (periodOnePotential a) z)^2-4
    rw [(canonicalDiscriminant_sq_eq_four_iff_finite hp hp1 _ (periodOnePotential_mem a) z).mpr hz]
    ring
  exact ⟨hq,rfl,(spectralCurve_regular_iff_simple hp hp1 a).mpr hsimple _ hq⟩

end NLS.Articles.DNLSEstimates
