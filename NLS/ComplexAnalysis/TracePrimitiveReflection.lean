import NLS.ComplexAnalysis.TracePrimitiveContinuation
import Mathlib.Topology.Algebra.Field

/-! # Schwarz reflection of source-normalized trace primitives

The input is symmetry of the actual trace along the real source segment,
with the fixed free normalization. Connectedness fixes the root sign;
uniqueness of continuous logarithms fixes the primitive itself.
-/

noncomputable section
open Set Complex
open scoped ComplexConjugate
namespace NLS.ComplexAnalysis.TracePrimitiveFamily
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]
variable (f : NLS.ComplexAnalysis.TracePrimitiveFamily A)

structure SourceSchwarzData (q : A) : Prop where
  domain_conj : ∀ z ∈ f.freeDomain, conj z ∈ f.freeDomain
  free_conj : ∀ z ∈ f.freeDomain, f.freePrimitive (conj z) = -conj (f.freePrimitive z)
  trace_conj : ∀ s : ℝ, ∀ z : ℂ, f.trace (conj z,(s : ℂ) • q) =
    conj (f.trace (z,(s : ℂ) • q))

variable {f} {q : A}

theorem SourceSchwarzData.radicand_conj (h : f.SourceSchwarzData q) (s : ℝ) (z : ℂ) :
    f.radicand (conj z,(s : ℂ) • q) = conj (f.radicand (z,(s : ℂ) • q)) := by
  simp only [radicand,h.trace_conj,map_sub,map_pow,map_ofNat]

theorem SourceSchwarzData.continuation_conj (h : f.SourceSchwarzData q) (z : ℂ)
    (ht : (z,q) ∈ f.continuationDomain) : (conj z,q) ∈ f.continuationDomain := by
  intro s hs
  have hh := ht s hs
  simp only [sourceSegmentMap,zero_add,sub_zero] at hh ⊢
  refine ⟨h.domain_conj z hh.1,?_⟩
  rw [h.radicand_conj]
  intro hz
  apply hh.2
  simpa only [conj_conj,map_zero] using congrArg conj hz

theorem continuousOn_source_path (G : ℂ × A → ℂ)
    (hG : ContinuousOn G f.continuationDomain) (z : ℂ) (q : A)
    (ht : (z,q) ∈ f.continuationDomain) :
    ContinuousOn (fun s : ℝ => G (z,(s : ℂ) • q)) (Icc (0 : ℝ) 1) := by
  apply hG.comp (by fun_prop)
  intro s hs
  simpa only [sourceSegmentMap,zero_add,sub_zero] using f.continuationDomain_segment (z,q) ht s hs

theorem SourceSchwarzData.root_conj_path (h : f.SourceSchwarzData q) (z : ℂ)
    (ht : (z,q) ∈ f.continuationDomain) :
    EqOn (fun s : ℝ => f.root (conj z,(s : ℂ) • q))
      (fun s : ℝ => -conj (f.root (z,(s : ℂ) • q))) (Icc (0 : ℝ) 1) := by
  have htc := h.continuation_conj z ht
  have hpath (w : ℂ) (hw : (w,q) ∈ f.continuationDomain) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (w,(s : ℂ) • q) ∈ f.continuationDomain := by
    simpa only [sourceSegmentMap,zero_add,sub_zero] using f.continuationDomain_segment (w,q) hw s hs
  have hc := continuousOn_source_path _ f.analytic_root.continuousOn z q ht
  have hcc := continuousOn_source_path _ f.analytic_root.continuousOn (conj z) q htc
  apply isPreconnected_Icc.eq_of_sq_eq hcc hc.star.neg ?_ ?_
    (y := (0 : ℝ)) (by constructor <;> norm_num) ?_
  · intro s hs
    change f.root (conj z,(s : ℂ) • q)^2 = (-conj (f.root (z,(s : ℂ) • q)))^2
    rw [f.root_sq _ (hpath _ htc s hs),neg_sq,← map_pow,
      f.root_sq _ (hpath _ ht s hs),h.radicand_conj]
  · intro s hs hz
    change -conj (f.root (z,(s : ℂ) • q)) = 0 at hz
    apply f.root_ne_zero _ (hpath _ ht s hs)
    simpa only [conj_conj,map_zero] using congrArg conj (neg_eq_zero.mp hz)
  · change f.root (conj z,((0 : ℝ) : ℂ) • q) = -conj (f.root (z,((0 : ℝ) : ℂ) • q))
    simp only [ofReal_zero,zero_smul ℂ q,f.root_base,freeRoot,
      h.free_conj z (f.continuationDomain_subset ht).1,sinh_neg,sinh_conj,map_mul,map_ofNat]
    ring

theorem SourceSchwarzData.root_conj (h : f.SourceSchwarzData q) (z : ℂ)
    (ht : (z,q) ∈ f.continuationDomain) : f.root (conj z,q) = -conj (f.root (z,q)) := by
  simpa only [ofReal_one,one_smul] using
    h.root_conj_path z ht (by constructor <;> norm_num : (1 : ℝ) ∈ Icc 0 1)

theorem SourceSchwarzData.primitive_conj (h : f.SourceSchwarzData q) (z : ℂ)
    (ht : (z,q) ∈ f.continuationDomain) :
    f.primitive (conj z,q) = -conj (f.primitive (z,q)) := by
  have htc := h.continuation_conj z ht
  have hpath (w : ℂ) (hw : (w,q) ∈ f.continuationDomain) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (w,(s : ℂ) • q) ∈ f.continuationDomain := by
    simpa only [sourceSegmentMap,zero_add,sub_zero] using f.continuationDomain_segment (w,q) hw s hs
  have hc := continuousOn_source_path _ f.analytic_primitive.continuousOn z q ht
  have hcc := continuousOn_source_path _ f.analytic_primitive.continuousOn (conj z) q htc
  have he := continuousLogarithms_eqOn
    (fun s : ℝ => f.primitive (conj z,(s : ℂ) • q))
    (fun s : ℝ => -conj (f.primitive (z,(s : ℂ) • q)))
    (Icc (0 : ℝ) 1) isPreconnected_Icc hcc hc.star.neg (by
      intro s hs
      have htr := f.primitive_trace _ (hpath _ ht s hs)
      rw [f.exp_primitive _ (hpath _ htc s hs)]
      dsimp only [multiplier]
      have hroot : f.root (conj z,(s : ℂ) • q) = -conj (f.root (z,(s : ℂ) • q)) :=
        h.root_conj_path z ht hs
      rw [h.trace_conj,hroot]
      rw [← sub_eq_add_neg]
      have heq : (f.trace (z,(s : ℂ) • q)-f.root (z,(s : ℂ) • q))/2 =
          exp (-f.primitive (z,(s : ℂ) • q)) := by
        rw [← htr.1,← htr.2]
        rw [show (2*cosh (f.primitive (z,(s : ℂ) • q))-
          2*sinh (f.primitive (z,(s : ℂ) • q)))/2 =
          cosh (f.primitive (z,(s : ℂ) • q))-sinh (f.primitive (z,(s : ℂ) • q)) by ring,
          cosh_sub_sinh]
      simpa only [map_div₀,map_sub,map_ofNat,← exp_conj,map_neg] using congrArg conj heq)
    0 (by constructor <;> norm_num) (by
      simp only [ofReal_zero,zero_smul ℂ q,f.primitive_base]
      exact h.free_conj z (f.continuationDomain_subset ht).1)
  simpa only [ofReal_one,one_smul] using he (by constructor <;> norm_num : (1 : ℝ) ∈ Icc 0 1)

end NLS.ComplexAnalysis.TracePrimitiveFamily
