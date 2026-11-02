import NLS.ComplexAnalysis.TracePrimitiveContinuation
import Mathlib.Topology.Algebra.Field

/-! # Source-normalized trace primitives commute with linear realization

Equality of traces and free normalizations fixes the continued root and
logarithm under every bounded complex linear map of source spaces.
The proof uses connected source paths and does not select new branches.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis.TracePrimitiveFamily
variable {A B : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup B] [NormedSpace ℂ B]

def pullback (g : TracePrimitiveFamily B) (L : A →L[ℂ] B) : TracePrimitiveFamily A where
  trace := fun t => g.trace (t.1,L t.2)
  analytic_trace := fun t _ => (g.analytic_trace (t.1,L t.2) (mem_univ _)).comp
    (f := fun t : ℂ × A => (t.1,L t.2)) (analyticAt_fst.prod ((L.analyticAt _).comp analyticAt_snd))
  freePrimitive := g.freePrimitive
  freeDomain := g.freeDomain
  isOpen_freeDomain := g.isOpen_freeDomain
  analytic_freePrimitive := g.analytic_freePrimitive
  free_trace := fun z => by simpa only [map_zero] using g.free_trace z

variable (f : TracePrimitiveFamily A) (g : TracePrimitiveFamily B) (L : A →L[ℂ] B)
  (htrace : ∀ z a, g.trace (z,L a) = f.trace (z,a))
  (hfree : ∀ z, g.freePrimitive z = f.freePrimitive z)
  (hdom : g.freeDomain = f.freeDomain)

include htrace in
theorem radicand_comp (z : ℂ) (a : A) : g.radicand (z,L a) = f.radicand (z,a) := by
  simp only [radicand,htrace]

include htrace hdom in
theorem continuationDomain_comp_iff (z : ℂ) (a : A) :
    (z,L a) ∈ g.continuationDomain ↔ (z,a) ∈ f.continuationDomain := by
  have hr (s : ℝ) : g.radicand (z,(s : ℂ) • L a) = f.radicand (z,(s : ℂ) • a) := by
    rw [← map_smul]
    exact radicand_comp f g L htrace z _
  constructor
  · intro ht s hs
    have hh := ht s hs
    simp only [sourceSegmentMap,zero_add,sub_zero] at hh ⊢
    change z ∈ g.freeDomain ∧ g.radicand (z,(s : ℂ) • L a) ≠ 0 at hh
    change z ∈ f.freeDomain ∧ f.radicand (z,(s : ℂ) • a) ≠ 0
    simpa only [hdom,hr] using hh
  · intro ht s hs
    have hh := ht s hs
    simp only [sourceSegmentMap,zero_add,sub_zero] at hh ⊢
    change z ∈ f.freeDomain ∧ f.radicand (z,(s : ℂ) • a) ≠ 0 at hh
    change z ∈ g.freeDomain ∧ g.radicand (z,(s : ℂ) • L a) ≠ 0
    simpa only [hdom,hr] using hh

include htrace hfree hdom in
theorem root_comp (z : ℂ) (a : A) (ht : (z,a) ∈ f.continuationDomain) :
    g.root (z,L a) = f.root (z,a) := by
  let p : ℝ → ℂ × A := fun s => (z,(s : ℂ) • a)
  let q : ℝ → ℂ × B := fun s => (z,L ((s : ℂ) • a))
  have hp (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : p s ∈ f.continuationDomain := by
    simpa only [p,sourceSegmentMap,zero_add,sub_zero] using f.continuationDomain_segment (z,a) ht s hs
  have hq (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : q s ∈ g.continuationDomain :=
    (continuationDomain_comp_iff f g L htrace hdom z _).mpr (hp s hs)
  have hpc : Continuous p := by dsimp only [p]; fun_prop
  have hqc : Continuous q := by dsimp only [q]; fun_prop
  have he := (convex_Icc (0 : ℝ) 1).isPreconnected.eq_of_sq_eq
    (g.analytic_root.continuousOn.comp hqc.continuousOn hq)
    (f.analytic_root.continuousOn.comp hpc.continuousOn hp)
    (fun s hs => by
      change g.root (q s)^2 = f.root (p s)^2
      rw [g.root_sq _ (hq s hs),f.root_sq _ (hp s hs)]
      exact radicand_comp f g L htrace z _)
    (fun {s} hs => f.root_ne_zero _ (hp s hs))
    (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) (by
      simp only [Function.comp_apply,p,q,ofReal_zero,zero_smul,map_zero,root_base,freeRoot,hfree])
  simpa only [Function.comp_apply,p,q,ofReal_one,one_smul] using he (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)

include htrace hfree hdom in
theorem primitive_comp (z : ℂ) (a : A) (ht : (z,a) ∈ f.continuationDomain) :
    g.primitive (z,L a) = f.primitive (z,a) := by
  let p : ℝ → ℂ × A := fun s => (z,(s : ℂ) • a)
  let q : ℝ → ℂ × B := fun s => (z,L ((s : ℂ) • a))
  have hp (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : p s ∈ f.continuationDomain := by
    simpa only [p,sourceSegmentMap,zero_add,sub_zero] using f.continuationDomain_segment (z,a) ht s hs
  have hq (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : q s ∈ g.continuationDomain :=
    (continuationDomain_comp_iff f g L htrace hdom z _).mpr (hp s hs)
  have hpc : Continuous p := by dsimp only [p]; fun_prop
  have hqc : Continuous q := by dsimp only [q]; fun_prop
  have he := continuousLogarithms_eqOn (g.primitive ∘ q) (f.primitive ∘ p) (Icc (0 : ℝ) 1)
    (convex_Icc (0 : ℝ) 1).isPreconnected
    (g.analytic_primitive.continuousOn.comp hqc.continuousOn hq)
    (f.analytic_primitive.continuousOn.comp hpc.continuousOn hp)
    (fun s hs => by
      rw [Function.comp_apply,Function.comp_apply,g.exp_primitive _ (hq s hs),f.exp_primitive _ (hp s hs)]
      change (g.trace (z,L ((s : ℂ) • a))+g.root (z,L ((s : ℂ) • a)))/2 =
        (f.trace (z,(s : ℂ) • a)+f.root (z,(s : ℂ) • a))/2
      rw [htrace,root_comp f g L htrace hfree hdom z _ (hp s hs)])
    0 (by constructor <;> norm_num) (by
      simp only [Function.comp_apply,p,q,ofReal_zero,zero_smul,map_zero,primitive_base,hfree])
  simpa only [Function.comp_apply,p,q,ofReal_one,one_smul] using
    he (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)

end NLS.ComplexAnalysis.TracePrimitiveFamily
