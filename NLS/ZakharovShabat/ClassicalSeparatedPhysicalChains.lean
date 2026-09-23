import NLS.ZakharovShabat.ClassicalSeparatedJets
import NLS.ZakharovShabat.ClassicalIntervalRootSpaces
import NLS.ZakharovShabat.ClassicalIntervalMultiplicity

/-!
# Physical interval representatives of separated scalar jets

The scalar Taylor kernel supplies endpoint conditions for the continuous
finite chains. This file constructs their actual `C¹` physical functions on
the interval and relates the forced recursion to the original differential
pencil, preparing the comparison with physical generalized eigenspaces.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier NLS.ComplexAnalysis
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- A real-line representative of every finite initial-value chain level. -/
def classicalJetSolution (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℕ → ℂ × ℂ) :
    ℕ → ℝ → ℂ × ℂ
  | 0 => classicalSolution Φ z (v 0)
  | n+1 => classicalForcedSolution Φ z (classicalJetCurve Φ z v n) (v (n+1))

/-- The physical representative and the continuous curve agree at every point of `[0,1]`. -/
theorem classicalJetSolution_restrict (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (v : ℕ → ℂ × ℂ) (n : ℕ) (t : Icc (0 : ℝ) 1) :
    classicalJetSolution Φ z v n t = classicalJetCurve Φ z v n t := by
  cases n with
  | zero => exact (classicalSolutionCurve_apply Φ z (v 0) t).symm
  | succ n => exact (classicalJetCurve_succ_apply Φ z v n t).symm

/-- Each level is `C¹`, independently of any endpoint conditions. -/
theorem contDiff_classicalJetSolution (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (v : ℕ → ℂ × ℂ) (n : ℕ) : ContDiff ℝ 1 (classicalJetSolution Φ z v n) := by
  cases n with
  | zero => exact contDiff_classicalSolution Φ z (v 0)
  | succ n => exact contDiff_classicalForcedSolution Φ z (classicalJetCurve Φ z v n) (v (n+1))

/-- The initial value at level `n` is exactly the prescribed vector. -/
theorem classicalJetSolution_initial (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (v : ℕ → ℂ × ℂ) (n : ℕ) : classicalJetSolution Φ z v n 0 = v n := by
  rw [classicalJetSolution_restrict Φ z v n ⟨0,by norm_num⟩,
    classicalJetCurve_initial]

/-- The zeroth level solves the homogeneous original physical equation. -/
theorem physicalPencil_classicalJetSolution_zero (Φ : Curve (ℂ × ℂ))
    (z : ℂ) (v : ℕ → ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    z • classicalJetSolution Φ z v 0 t -
      physicalOperator (extend Φ) (classicalJetSolution Φ z v 0) t = 0 := by
  change z • classicalSolution Φ z (v 0) t -
      physicalOperator (extend Φ) (classicalSolution Φ z (v 0)) t = 0
  rw [physicalOperator_classicalSolution,sub_self]

/-- Successive physical levels obey the actual original `z-L` recursion. -/
theorem physicalPencil_classicalJetSolution_succ (Φ : Curve (ℂ × ℂ))
    (z : ℂ) (v : ℕ → ℂ × ℂ) (n : ℕ) (t : Icc (0 : ℝ) 1) :
    z • classicalJetSolution Φ z v (n+1) t -
      physicalOperator (extend Φ) (classicalJetSolution Φ z v (n+1)) t =
        classicalJetSolution Φ z v n t := by
  change z • classicalForcedSolution Φ z (classicalJetCurve Φ z v n) (v (n+1)) t -
      physicalOperator (extend Φ)
        (classicalForcedSolution Φ z (classicalJetCurve Φ z v n) (v (n+1))) t = _
  rw [physicalPencil_classicalForcedSolution,
    classicalJetSolution_restrict Φ z v n t]

/-- A scalar jet in the Taylor kernel gives a genuine original interval-domain
function at each level of the chain. -/
theorem hasClassicalIntervalDomain_classicalSeparatedJet (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (N : ℕ) (w : Fin N → ℂ)
    (hw : w ∈ LinearMap.ker
      (scalarTaylorJetMap (scalarFormalTaylor (classicalSeparatedEndpointSeries b Φ z)) N))
    (k : Fin N) :
    HasClassicalIntervalDomain b
      (classicalJetSolution Φ z (separatedSignedInitialJet b N w) k.val) := by
  let v := separatedSignedInitialJet b N w
  have hc := contDiff_classicalJetSolution Φ z v k.val
  refine ⟨hasIntervalH1Regularity_of_contDiff hc.fst,
    hasIntervalH1Regularity_of_contDiff hc.snd,?_,?_⟩
  · rw [classicalJetSolution_initial]
    exact sub_eq_zero.mp (separatedSignedInitialJet_left_condition b N w k.val)
  · have hr := (mem_ker_classicalSeparatedTaylorJetMap_iff b Φ z N w).mp hw k
    rw [← classicalJetSolution_restrict Φ z v k.val ⟨1,by norm_num⟩] at hr
    exact sub_eq_zero.mp hr

/-- All physical jet representatives are square integrable on the original interval. -/
theorem memLp_classicalJetSolution (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (v : ℕ → ℂ × ℂ) (n : ℕ) :
    MemLp (classicalJetSolution Φ z v n) 2 (volume.restrict (Ioc 0 1)) := by
  have hc := contDiff_classicalJetSolution Φ z v n
  exact memLp_prod_iff.mpr
    ⟨memLp_of_intervalH1Regularity (hasIntervalH1Regularity_of_contDiff hc.fst),
      memLp_of_intervalH1Regularity (hasIntervalH1Regularity_of_contDiff hc.snd)⟩

/-- The original physical `L²` class of a classical initial-value chain level. -/
def classicalJetPhysical (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (v : ℕ → ℂ × ℂ) (n : ℕ) : IntervalPairL2 :=
  intervalL2OfFunction (classicalJetSolution Φ z v n) (memLp_classicalJetSolution Φ z v n)

private theorem intervalL2Representative_sub (u v : IntervalPairL2) :
    intervalL2Representative (u-v) =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x => intervalL2Representative u x-intervalL2Representative v x) := by
  filter_upwards [Lp.coeFn_sub u.ofLp.1 v.ofLp.1,
    Lp.coeFn_sub u.ofLp.2 v.ofLp.2] with x h₁ h₂
  exact Prod.ext h₁ h₂

/-- A pointwise original pencil equation gives the exact physical `L²` pencil equality. -/
theorem classicalPencil_of_pointwise_equation (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1)))
    (z : ℂ) (f g : ℝ → ℂ × ℂ) (hf : HasClassicalIntervalDomain b f)
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1)))
    (he : ∀ t : Icc (0 : ℝ) 1,
      z • f t - physicalOperator (extend Φ) f t = g t) :
    classicalPencil b (intervalL2OfFunction (extend Φ) hΦ) z
      (classicalDomainOfFunction b f hf) = intervalL2OfFunction g hg := by
  have hL : MemLp f 2 (volume.restrict (Ioc 0 1)) :=
    memLp_prod_iff.mpr ⟨memLp_of_intervalH1Regularity hf.fst_regular,
      memLp_of_intervalH1Regularity hf.snd_regular⟩
  rw [classicalPencil_apply,classicalInclusion_ofFunction b f hf hL]
  apply intervalL2Representative_injective
  have hop := classicalOperator_realization_ofFunction b (extend Φ) f hΦ hf
  filter_upwards [intervalL2Representative_sub
      (z • intervalL2OfFunction f hL)
      (classicalOperator b (intervalL2OfFunction (extend Φ) hΦ)
        (classicalDomainOfFunction b f hf)),
    intervalL2Representative_smul z (intervalL2OfFunction f hL),
    intervalL2Representative_ofFunction f hL,hop,
    intervalL2Representative_ofFunction g hg,
    ae_restrict_mem measurableSet_Ioc] with t hsub hsmul hfr hop' hgr ht
  rw [hsub,hsmul,hfr,hop',hgr]
  exact he ⟨t,Ioc_subset_Icc_self ht⟩

/-- The zeroth physical chain level is in the kernel of the original interval pencil. -/
theorem classicalPencil_classicalJetSolution_zero (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1)))
    (z : ℂ) (v : ℕ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b (classicalJetSolution Φ z v 0)) :
    classicalPencil b (intervalL2OfFunction (extend Φ) hΦ) z
      (classicalDomainOfFunction b (classicalJetSolution Φ z v 0) hf) = 0 := by
  have h := classicalPencil_of_pointwise_equation b Φ hΦ z
    (classicalJetSolution Φ z v 0) 0 hf (by simp)
    (physicalPencil_classicalJetSolution_zero Φ z v)
  have h0 : intervalL2Representative (0 : IntervalPairL2) =ᵐ[volume.restrict (Ioc 0 1)]
      (0 : ℝ → ℂ × ℂ) := by
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc 0 1))] with t ht
    exact Prod.ext ht ht
  have hz : intervalL2OfFunction (0 : ℝ → ℂ × ℂ) (by simp) = 0 := by
    apply intervalL2Representative_injective
    exact (intervalL2Representative_ofFunction (0 : ℝ → ℂ × ℂ) (by simp)).trans h0.symm
  rw [hz] at h
  exact h

/-- At every positive level, the original physical pencil maps the chain to its predecessor. -/
theorem classicalPencil_classicalJetSolution_succ (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1)))
    (z : ℂ) (v : ℕ → ℂ × ℂ) (n : ℕ)
    (hf : HasClassicalIntervalDomain b (classicalJetSolution Φ z v (n+1))) :
    classicalPencil b (intervalL2OfFunction (extend Φ) hΦ) z
      (classicalDomainOfFunction b (classicalJetSolution Φ z v (n+1)) hf) =
        classicalJetPhysical Φ z v n :=
  classicalPencil_of_pointwise_equation b Φ hΦ z
    (classicalJetSolution Φ z v (n+1)) (classicalJetSolution Φ z v n) hf
    (memLp_classicalJetSolution Φ z v n)
    (physicalPencil_classicalJetSolution_succ Φ z v n)

/-- Every scalar kernel jet produces a root vector of the actual physical
interval operator at its corresponding chain length. -/
theorem classicalJetPhysical_mem_rootSpace_of_scalarKernel (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1)))
    (z : ℂ) (N : ℕ) (w : Fin N → ℂ)
    (hw : w ∈ LinearMap.ker
      (scalarTaylorJetMap (scalarFormalTaylor (classicalSeparatedEndpointSeries b Φ z)) N))
    (k : Fin N) :
    classicalJetPhysical Φ z (separatedSignedInitialJet b N w) k.val ∈
      b.classicalRootSpace (intervalL2OfFunction (extend Φ) hΦ) z (k.val+1) := by
  let v := separatedSignedInitialJet b N w
  let u := intervalL2OfFunction (extend Φ) hΦ
  have hdom (j : ℕ) (hj : j < N) :
      HasClassicalIntervalDomain b (classicalJetSolution Φ z v j) :=
    hasClassicalIntervalDomain_classicalSeparatedJet b Φ z N w hw ⟨j,hj⟩
  have hrec : ∀ n : ℕ, n < N →
      classicalJetPhysical Φ z v n ∈ b.classicalRootSpace u z (n+1) := by
    intro n
    induction n with
    | zero =>
      intro hn
      rw [b.mem_classicalRootSpace_succ]
      refine ⟨classicalDomainOfFunction b (classicalJetSolution Φ z v 0) (hdom 0 hn), ?_, ?_⟩
      · exact classicalInclusion_ofFunction b (classicalJetSolution Φ z v 0)
          (hdom 0 hn) (memLp_classicalJetSolution Φ z v 0)
      · rw [classicalPencil_classicalJetSolution_zero b Φ hΦ z v (hdom 0 hn)]
        exact Submodule.zero_mem _
    | succ n ih =>
      intro hn
      have hn' : n < N := by omega
      rw [b.mem_classicalRootSpace_succ]
      refine ⟨classicalDomainOfFunction b (classicalJetSolution Φ z v (n+1))
        (hdom (n+1) hn), ?_, ?_⟩
      · exact classicalInclusion_ofFunction b (classicalJetSolution Φ z v (n+1))
          (hdom (n+1) hn) (memLp_classicalJetSolution Φ z v (n+1))
      · rw [classicalPencil_classicalJetSolution_succ b Φ hΦ z v n (hdom (n+1) hn)]
        exact ih hn'
  exact hrec k.val k.isLt

/-- Equal physical chain levels in the scalar kernel have the same original
interval-domain representative. -/
private theorem classicalSeparatedJet_domain_eq_of_physical_eq
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (N : ℕ) (u v : Fin N → ℂ)
    (hu : u ∈ LinearMap.ker
      (scalarTaylorJetMap (scalarFormalTaylor (classicalSeparatedEndpointSeries b Φ z)) N))
    (hv : v ∈ LinearMap.ker
      (scalarTaylorJetMap (scalarFormalTaylor (classicalSeparatedEndpointSeries b Φ z)) N))
    (n : ℕ) (hn : n < N)
    (he : classicalJetPhysical Φ z (separatedSignedInitialJet b N u) n =
      classicalJetPhysical Φ z (separatedSignedInitialJet b N v) n) :
    classicalDomainOfFunction b
        (classicalJetSolution Φ z (separatedSignedInitialJet b N u) n)
        (hasClassicalIntervalDomain_classicalSeparatedJet b Φ z N u hu ⟨n,hn⟩) =
      classicalDomainOfFunction b
        (classicalJetSolution Φ z (separatedSignedInitialJet b N v) n)
        (hasClassicalIntervalDomain_classicalSeparatedJet b Φ z N v hv ⟨n,hn⟩) := by
  apply classicalInclusion_injective b
  rw [classicalInclusion_ofFunction,classicalInclusion_ofFunction]
  exact he

/-- The physical class of one chain level determines its scalar initial coefficient. -/
private theorem classicalSeparatedJet_initial_eq_of_physical_eq
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (N : ℕ) (u v : Fin N → ℂ)
    (hu : u ∈ LinearMap.ker
      (scalarTaylorJetMap (scalarFormalTaylor (classicalSeparatedEndpointSeries b Φ z)) N))
    (hv : v ∈ LinearMap.ker
      (scalarTaylorJetMap (scalarFormalTaylor (classicalSeparatedEndpointSeries b Φ z)) N))
    (n : ℕ) (hn : n < N)
    (he : classicalJetPhysical Φ z (separatedSignedInitialJet b N u) n =
      classicalJetPhysical Φ z (separatedSignedInitialJet b N v) n) :
      u ⟨n,hn⟩ = v ⟨n,hn⟩ := by
  have hd := classicalSeparatedJet_domain_eq_of_physical_eq b Φ z N u v hu hv n hn he
  have h0 := congrArg (fun f : ClassicalIntervalDomain b => f.val ⟨0,by norm_num⟩) hd
  change classicalJetSolution Φ z (separatedSignedInitialJet b N u) n 0 =
    classicalJetSolution Φ z (separatedSignedInitialJet b N v) n 0 at h0
  rw [classicalJetSolution_initial,classicalJetSolution_initial] at h0
  have hfirst := congrArg Prod.fst h0
  simp only [separatedSignedInitialJet,dif_pos hn,Prod.smul_fst,smul_eq_mul,mul_one] at hfirst
  exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) hfirst

/-- Equality of physical chain levels descends one step through the actual
original interval pencil. -/
private theorem classicalSeparatedJet_prev_eq_of_physical_eq
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1))) (z : ℂ)
    (N : ℕ) (u v : Fin N → ℂ)
    (hu : u ∈ LinearMap.ker
      (scalarTaylorJetMap (scalarFormalTaylor (classicalSeparatedEndpointSeries b Φ z)) N))
    (hv : v ∈ LinearMap.ker
      (scalarTaylorJetMap (scalarFormalTaylor (classicalSeparatedEndpointSeries b Φ z)) N))
    (n : ℕ) (hn : n+1 < N)
    (he : classicalJetPhysical Φ z (separatedSignedInitialJet b N u) (n+1) =
      classicalJetPhysical Φ z (separatedSignedInitialJet b N v) (n+1)) :
    classicalJetPhysical Φ z (separatedSignedInitialJet b N u) n =
      classicalJetPhysical Φ z (separatedSignedInitialJet b N v) n := by
  have hd := classicalSeparatedJet_domain_eq_of_physical_eq b Φ z N u v hu hv (n+1) hn he
  rw [← classicalPencil_classicalJetSolution_succ b Φ hΦ z
      (separatedSignedInitialJet b N u) n
      (hasClassicalIntervalDomain_classicalSeparatedJet b Φ z N u hu ⟨n+1,hn⟩),
    ← classicalPencil_classicalJetSolution_succ b Φ hΦ z
      (separatedSignedInitialJet b N v) n
      (hasClassicalIntervalDomain_classicalSeparatedJet b Φ z N v hv ⟨n+1,hn⟩),hd]

/-- Equality of top physical vectors determines every scalar initial
coefficient in their finite chains. -/
theorem classicalSeparatedJet_initial_unique_of_physical_eq
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1))) (z : ℂ)
    (N : ℕ) (u v : Fin N → ℂ)
    (hu : u ∈ LinearMap.ker
      (scalarTaylorJetMap (scalarFormalTaylor (classicalSeparatedEndpointSeries b Φ z)) N))
    (hv : v ∈ LinearMap.ker
      (scalarTaylorJetMap (scalarFormalTaylor (classicalSeparatedEndpointSeries b Φ z)) N))
    (n : ℕ) : n < N →
    classicalJetPhysical Φ z (separatedSignedInitialJet b N u) n =
      classicalJetPhysical Φ z (separatedSignedInitialJet b N v) n →
    ∀ j (_hj : j ≤ n) (hjN : j < N), u ⟨j,hjN⟩ = v ⟨j,hjN⟩ := by
  induction n with
  | zero =>
    intro hn he j hj hjN
    have hj0 : j = 0 := by omega
    subst j
    exact classicalSeparatedJet_initial_eq_of_physical_eq b Φ z N u v hu hv 0 hn he
  | succ n ih =>
    intro hn he j hj hjN
    by_cases hjn : j ≤ n
    · exact ih (by omega)
        (classicalSeparatedJet_prev_eq_of_physical_eq b Φ hΦ z N u v hu hv n hn he)
        j hjn hjN
    · have hj' : j = n+1 := by omega
      subst j
      exact classicalSeparatedJet_initial_eq_of_physical_eq b Φ z N u v hu hv (n+1) hn he

/-- The physical top vector faithfully encodes every coefficient of a
scalar Taylor kernel jet. -/
theorem classicalJetPhysical_injective_on_scalarKernel (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1))) (z : ℂ)
    (n : ℕ) : Function.Injective
      (fun w : LinearMap.ker (scalarTaylorJetMap
          (scalarFormalTaylor (classicalSeparatedEndpointSeries b Φ z)) (n+1)) =>
        classicalJetPhysical Φ z (separatedSignedInitialJet b (n+1) w.val) n) := by
  intro u v he
  apply Subtype.ext
  funext j
  exact classicalSeparatedJet_initial_unique_of_physical_eq b Φ hΦ z (n+1)
    u.val v.val u.property v.property n (Nat.lt_succ_self n) he j.val
    (Nat.le_of_lt_succ j.isLt) j.isLt

/-- Homogeneous solution curves depend linearly on their initial vectors. -/
private theorem classicalSolutionCurve_add_initial (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (a c : ℂ × ℂ) :
    classicalSolutionCurve Φ z (a+c) =
      classicalSolutionCurve Φ z a + classicalSolutionCurve Φ z c := by
  simp only [classicalSolutionCurve_eq_inverse]
  have hconst : ContinuousMap.const (Icc (0 : ℝ) 1) (a+c) =
      ContinuousMap.const (Icc (0 : ℝ) 1) a + ContinuousMap.const (Icc (0 : ℝ) 1) c := by
    ext t <;> simp
  rw [hconst,map_add]

private theorem classicalSolutionCurve_smul_initial (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (c : ℂ) (a : ℂ × ℂ) :
    classicalSolutionCurve Φ z (c • a) = c • classicalSolutionCurve Φ z a := by
  simp only [classicalSolutionCurve_eq_inverse]
  have hconst : ContinuousMap.const (Icc (0 : ℝ) 1) (c • a) =
      c • ContinuousMap.const (Icc (0 : ℝ) 1) a := by
    ext t <;> simp
  rw [hconst,map_smul]

/-- The whole forced chain is additive in its prescribed initial jet. -/
theorem classicalJetCurve_add_initial (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (v w : ℕ → ℂ × ℂ) (n : ℕ) :
    classicalJetCurve Φ z (v+w) n =
      classicalJetCurve Φ z v n + classicalJetCurve Φ z w n := by
  induction n with
  | zero =>
    simp only [classicalJetCurve_zero,Pi.add_apply,classicalSolutionCurve_add_initial]
  | succ n ih =>
    rw [classicalJetCurve_succ,classicalJetCurve_succ,classicalJetCurve_succ,
      Pi.add_apply,classicalSolutionCurve_add_initial,ih,map_add]
    abel

/-- The whole forced chain is homogeneous in its prescribed initial jet. -/
theorem classicalJetCurve_smul_initial (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (c : ℂ) (v : ℕ → ℂ × ℂ) (n : ℕ) :
    classicalJetCurve Φ z (c • v) n = c • classicalJetCurve Φ z v n := by
  induction n with
  | zero =>
    simp only [classicalJetCurve_zero,Pi.smul_apply,classicalSolutionCurve_smul_initial]
  | succ n ih =>
    rw [classicalJetCurve_succ,classicalJetCurve_succ,Pi.smul_apply,
      classicalSolutionCurve_smul_initial,ih,map_smul]
    exact (smul_add c (classicalSolutionCurve Φ z (v (n+1)))
      (classicalChainOperator Φ z (classicalJetCurve Φ z v n))).symm

/-- The signed boundary-line initial jet is additive. -/
theorem separatedSignedInitialJet_add (b : BoundaryCondition) (N : ℕ)
    (u v : Fin N → ℂ) :
    separatedSignedInitialJet b N (u+v) =
      separatedSignedInitialJet b N u + separatedSignedInitialJet b N v := by
  funext j
  by_cases hj : j < N
  · simp [separatedSignedInitialJet,hj,add_smul,mul_add]
  · simp [separatedSignedInitialJet,hj]

/-- The signed boundary-line initial jet is homogeneous. -/
theorem separatedSignedInitialJet_smul (b : BoundaryCondition) (N : ℕ)
    (c : ℂ) (u : Fin N → ℂ) :
    separatedSignedInitialJet b N (c • u) = c • separatedSignedInitialJet b N u := by
  funext j
  by_cases hj : j < N
  · simp [separatedSignedInitialJet,hj,mul_comm,mul_assoc]
    ring
  · simp [separatedSignedInitialJet,hj]

/-- Addition of physical chain representatives holds on the original interval. -/
private theorem classicalJetSolution_add_on_interval (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (v w : ℕ → ℂ × ℂ) (n : ℕ) (t : Icc (0 : ℝ) 1) :
    classicalJetSolution Φ z (v+w) n t =
      classicalJetSolution Φ z v n t + classicalJetSolution Φ z w n t := by
  rw [classicalJetSolution_restrict,classicalJetSolution_restrict,
    classicalJetSolution_restrict,classicalJetCurve_add_initial]
  rfl

/-- Scalar multiplication of physical chain representatives holds on the original interval. -/
private theorem classicalJetSolution_smul_on_interval (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (c : ℂ) (v : ℕ → ℂ × ℂ) (n : ℕ) (t : Icc (0 : ℝ) 1) :
    classicalJetSolution Φ z (c • v) n t = c • classicalJetSolution Φ z v n t := by
  rw [classicalJetSolution_restrict,classicalJetSolution_restrict,
    classicalJetCurve_smul_initial]
  rfl

/-- The physical `L²` chain level is additive in its initial jet. -/
theorem classicalJetPhysical_add_initial (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (v w : ℕ → ℂ × ℂ) (n : ℕ) :
    classicalJetPhysical Φ z (v+w) n =
      classicalJetPhysical Φ z v n + classicalJetPhysical Φ z w n := by
  apply intervalL2Representative_injective
  filter_upwards [intervalL2Representative_ofFunction
      (classicalJetSolution Φ z (v+w) n) (memLp_classicalJetSolution Φ z (v+w) n),
    intervalL2Representative_add (classicalJetPhysical Φ z v n) (classicalJetPhysical Φ z w n),
    intervalL2Representative_ofFunction
      (classicalJetSolution Φ z v n) (memLp_classicalJetSolution Φ z v n),
    intervalL2Representative_ofFunction
      (classicalJetSolution Φ z w n) (memLp_classicalJetSolution Φ z w n),
    ae_restrict_mem measurableSet_Ioc] with t hsum hadd hv hw ht
  unfold classicalJetPhysical
  unfold classicalJetPhysical at hadd
  rw [hsum,hadd,hv,hw]
  exact classicalJetSolution_add_on_interval Φ z v w n ⟨t,Ioc_subset_Icc_self ht⟩

/-- The physical `L²` chain level is homogeneous in its initial jet. -/
theorem classicalJetPhysical_smul_initial (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (c : ℂ) (v : ℕ → ℂ × ℂ) (n : ℕ) :
    classicalJetPhysical Φ z (c • v) n = c • classicalJetPhysical Φ z v n := by
  apply intervalL2Representative_injective
  filter_upwards [intervalL2Representative_ofFunction
      (classicalJetSolution Φ z (c • v) n) (memLp_classicalJetSolution Φ z (c • v) n),
    intervalL2Representative_smul c (classicalJetPhysical Φ z v n),
    intervalL2Representative_ofFunction
      (classicalJetSolution Φ z v n) (memLp_classicalJetSolution Φ z v n),
    ae_restrict_mem measurableSet_Ioc] with t hleft hsmul hv ht
  unfold classicalJetPhysical
  unfold classicalJetPhysical at hsmul
  rw [hleft,hsmul,hv]
  exact classicalJetSolution_smul_on_interval Φ z c v n ⟨t,Ioc_subset_Icc_self ht⟩

/-- Linear dependence of the physical chain level on all initial values. -/
def classicalJetPhysicalLinear (Φ : Curve (ℂ × ℂ)) (z : ℂ) (n : ℕ) :
    (ℕ → ℂ × ℂ) →ₗ[ℂ] IntervalPairL2 where
  toFun v := classicalJetPhysical Φ z v n
  map_add' := fun v w => classicalJetPhysical_add_initial Φ z v w n
  map_smul' := fun c v => classicalJetPhysical_smul_initial Φ z c v n

/-- Linear dependence of the signed boundary-line initial values on scalar coefficients. -/
def separatedSignedInitialJetLinear (b : BoundaryCondition) (N : ℕ) :
    (Fin N → ℂ) →ₗ[ℂ] (ℕ → ℂ × ℂ) where
  toFun w := separatedSignedInitialJet b N w
  map_add' := separatedSignedInitialJet_add b N
  map_smul' := separatedSignedInitialJet_smul b N

/-- Linear map from scalar Taylor kernel jets into finite physical boundary
root spaces, realized by the actual top chain vector. -/
def classicalSeparatedJetRootMap (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1)))
    (z : ℂ) (n : ℕ) :
    LinearMap.ker (scalarTaylorJetMap
      (scalarFormalTaylor (classicalSeparatedEndpointSeries b Φ z)) (n+1)) →ₗ[ℂ]
      ↥(b.classicalRootSpace (intervalL2OfFunction (extend Φ) hΦ) z (n+1)) where
  toFun w := ⟨classicalJetPhysical Φ z (separatedSignedInitialJet b (n+1) w.val) n,
    classicalJetPhysical_mem_rootSpace_of_scalarKernel b Φ hΦ z (n+1) w.val w.property
      ⟨n,Nat.lt_succ_self n⟩⟩
  map_add' u v := by
    apply Subtype.ext
    change classicalJetPhysical Φ z (separatedSignedInitialJet b (n+1) (u+v).val) n =
      classicalJetPhysical Φ z (separatedSignedInitialJet b (n+1) u.val) n +
        classicalJetPhysical Φ z (separatedSignedInitialJet b (n+1) v.val) n
    rw [Submodule.coe_add,separatedSignedInitialJet_add,classicalJetPhysical_add_initial]
  map_smul' c w := by
    apply Subtype.ext
    change classicalJetPhysical Φ z (separatedSignedInitialJet b (n+1) (c • w).val) n =
      c • classicalJetPhysical Φ z (separatedSignedInitialJet b (n+1) w.val) n
    rw [Submodule.coe_smul,separatedSignedInitialJet_smul,classicalJetPhysical_smul_initial]

/-- The map from scalar Taylor kernel to physical finite root space is injective. -/
theorem classicalSeparatedJetRootMap_injective (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1)))
    (z : ℂ) (n : ℕ) :
    Function.Injective (classicalSeparatedJetRootMap b Φ hΦ z n) := by
  intro u v he
  exact classicalJetPhysical_injective_on_scalarKernel b Φ hΦ z n
    (congrArg Subtype.val he)

/-- The scalar Taylor kernel cannot be larger than the full original
physical generalized eigenspace at any truncation length. -/
theorem finrank_classicalSeparatedTaylorKernel_le_physicalMultiplicity
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1)))
    (z : ℂ) (n : ℕ) :
    Module.finrank ℂ (LinearMap.ker (scalarTaylorJetMap
      (scalarFormalTaylor (classicalSeparatedEndpointSeries b Φ z)) (n+1))) ≤
      b.classicalAlgebraicMultiplicity
      (intervalL2OfFunction (extend Φ) hΦ) z := by
  let u := intervalL2OfFunction (extend Φ) hΦ
  let : FiniteDimensional ℂ (b.classicalRootSpaceTop u z) :=
    b.finiteDimensional_classicalRootSpaceTop u z
  have hsub : b.classicalRootSpace u z (n+1) ≤ b.classicalRootSpaceTop u z :=
    le_iSup (b.classicalRootSpace u z) (n+1)
  let f := (Submodule.inclusion hsub).comp
    (classicalSeparatedJetRootMap b Φ hΦ z n)
  have hf : Function.Injective f :=
    (Submodule.inclusion_injective hsub).comp
      (classicalSeparatedJetRootMap_injective b Φ hΦ z n)
  have hle := LinearMap.finrank_le_finrank_of_injective (f := f) hf
  simpa only [classicalAlgebraicMultiplicity] using hle

/-- The classical separated characteristic has finite analytic order at every
spectral parameter for every continuous physical potential. -/
theorem analyticOrderAt_classicalSeparated_ne_top (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1))) (z : ℂ) :
    analyticOrderAt (classicalSeparatedCharacteristic b Φ) z ≠ ⊤ := by
  intro ht
  let m := b.classicalAlgebraicMultiplicity (intervalL2OfFunction (extend Φ) hΦ) z
  have hzero : scalarFormalTaylor (classicalSeparatedEndpointSeries b Φ z) = 0 :=
    PowerSeries.order_eq_top.mp ((order_classicalSeparatedEndpointSeries b Φ z).trans ht)
  have hdim : Module.finrank ℂ (LinearMap.ker (scalarTaylorJetMap
      (scalarFormalTaylor (classicalSeparatedEndpointSeries b Φ z)) (m+1))) = m+1 := by
    rw [hzero,finrank_ker_scalarTaylorJetMap_zero]
  have hle := finrank_classicalSeparatedTaylorKernel_le_physicalMultiplicity b Φ hΦ z m
  rw [hdim] at hle
  exact Nat.not_succ_le_self m hle

/-- Every classical characteristic order is at most the actual physical
boundary algebraic multiplicity. -/
theorem analyticOrder_classicalSeparated_le_physicalMultiplicity
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1)))
    (z : ℂ) (m : ℕ)
    (hm : analyticOrderAt (classicalSeparatedCharacteristic b Φ) z = m) :
    m ≤ b.classicalAlgebraicMultiplicity
      (intervalL2OfFunction (extend Φ) hΦ) z := by
  have hdim := finrank_classicalSeparatedTaylorKernel b Φ z m (m+1) hm
  have hle := finrank_classicalSeparatedTaylorKernel_le_physicalMultiplicity b Φ hΦ z m
  rw [hdim,min_eq_right (Nat.le_succ m)] at hle
  exact hle

/-- The extended analytic order is finite and bounded by the physical
algebraic multiplicity, without a separately chosen natural order. -/
theorem analyticOrderAt_classicalSeparated_le_physicalMultiplicity
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1))) (z : ℂ) :
    analyticOrderAt (classicalSeparatedCharacteristic b Φ) z ≤
      (b.classicalAlgebraicMultiplicity
        (intervalL2OfFunction (extend Φ) hΦ) z : ℕ∞) := by
  obtain ⟨m,hm⟩ := ENat.ne_top_iff_exists.mp
    (analyticOrderAt_classicalSeparated_ne_top b Φ hΦ z)
  rw [← hm]
  exact_mod_cast analyticOrder_classicalSeparated_le_physicalMultiplicity b Φ hΦ z m hm.symm

end NLS.ZakharovShabat
