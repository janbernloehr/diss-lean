import NLS.ZakharovShabat.ClassicalDiscriminantCommutation
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-! # The actual monodromy variation along a discriminant Hamiltonian

The traceless transported monodromy acts on the original fundamental
solutions. Its differentiated action constructs the actual potential
variation without dividing by a spectral difference. Initial-value
uniqueness and the matching endpoints then give the monodromy commutator
identity, valid even at coincident spectral parameters.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex NLS.LinearVolterra
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- The traceless part of the transported monodromy, acting on a vector. -/
def classicalDiscriminantTransport (Φ : Curve (ℂ × ℂ)) (w : ℂ) (s : ℝ) (v : ℂ × ℂ) : ℂ × ℂ :=
  (classicalDiscriminantDiagonal Φ w s/2*v.1+I*(classicalDiscriminantGradient Φ w s).2*v.2,
    -I*(classicalDiscriminantGradient Φ w s).1*v.1-classicalDiscriminantDiagonal Φ w s/2*v.2)

/-- The transported monodromy action has matching physical endpoint values. -/
theorem classicalDiscriminantTransport_endpoints (Φ : Curve (ℂ × ℂ)) (w : ℂ) (v : ℂ × ℂ) :
    classicalDiscriminantTransport Φ w 1 v = classicalDiscriminantTransport Φ w 0 v := by
  simp [classicalDiscriminantTransport]

theorem continuous_classicalDiscriminantTransport_solution (Φ : Curve (ℂ × ℂ)) (z w : ℂ) (v : ℂ × ℂ) :
    Continuous (fun s => classicalDiscriminantTransport Φ w s (classicalSolution Φ z v s)) := by
  have hg := continuous_classicalDiscriminantGradient Φ w
  have hd := continuous_classicalDiscriminantDiagonal Φ w
  have hu := continuous_classicalSolution Φ z v
  unfold classicalDiscriminantTransport
  fun_prop

/-- Differentiating the transported action yields the signed forcing for
the discriminant Hamiltonian, multiplied by the spectral difference. -/
theorem hasDerivAt_classicalDiscriminantTransport_solution (Φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => classicalDiscriminantTransport Φ w s (classicalSolution Φ z v s))
      (classicalODECoefficient (Φ t) z
        (classicalDiscriminantTransport Φ w t (classicalSolution Φ z v t))+
        (2*(w-z)) • classicalPotentialVariationSource Φ (classicalDiscriminantHamiltonianDirection Φ w) z v t) t := by
  have hu := hasDerivAt_classicalSolution Φ z v t
  have hu₁ := HasFDerivAt.hasDerivAt hu.fst
  have hu₂ := HasFDerivAt.hasDerivAt hu.snd
  have hd := hasDerivAt_classicalDiscriminantDiagonal Φ w t
  have hg₁ := hasDerivAt_classicalDiscriminantGradient_fst Φ w t
  have hg₂ := hasDerivAt_classicalDiscriminantGradient_snd Φ w t
  have h := (((hd.div_const 2).mul hu₁).add ((hg₂.const_mul I).mul hu₂)).prodMk
    (((hg₁.const_mul (-I)).mul hu₁).sub ((hd.div_const 2).mul hu₂))
  convert! h using 1
  apply Prod.ext <;>
    simp only [classicalDiscriminantTransport,classicalODECoefficient_apply,
      classicalPotentialVariationSource_apply,classicalDiscriminantHamiltonianDirection,ContinuousMap.coe_mk,
      Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul] <;> dsimp <;>
    ring_nf <;> simp only [I_sq] <;> ring

/-- The commutator construction has zero initial value. -/
def classicalDiscriminantVariationNumerator (Φ : Curve (ℂ × ℂ)) (z w : ℂ) (v : ℂ × ℂ) (s : ℝ) : ℂ × ℂ :=
  classicalDiscriminantTransport Φ w s (classicalSolution Φ z v s)-
    classicalSolution Φ z (classicalDiscriminantTransport Φ w 0 v) s

@[simp] theorem classicalDiscriminantVariationNumerator_zero (Φ : Curve (ℂ × ℂ)) (z w : ℂ) (v : ℂ × ℂ) :
    classicalDiscriminantVariationNumerator Φ z w v 0 = 0 := by
  simp [classicalDiscriminantVariationNumerator]

theorem continuous_classicalDiscriminantVariationNumerator (Φ : Curve (ℂ × ℂ)) (z w : ℂ) (v : ℂ × ℂ) :
    Continuous (classicalDiscriminantVariationNumerator Φ z w v) :=
  (continuous_classicalDiscriminantTransport_solution Φ z w v).sub (continuous_classicalSolution _ _ _)

theorem hasDerivAt_classicalDiscriminantVariationNumerator (Φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    HasDerivAt (classicalDiscriminantVariationNumerator Φ z w v)
      (classicalODECoefficient (Φ t) z (classicalDiscriminantVariationNumerator Φ z w v t)+
        (2*(w-z)) • classicalPotentialVariationSource Φ (classicalDiscriminantHamiltonianDirection Φ w) z v t) t := by
  have h := (hasDerivAt_classicalDiscriminantTransport_solution Φ z w v t).sub
    (hasDerivAt_classicalSolution Φ z (classicalDiscriminantTransport Φ w 0 v) t)
  convert! h using 1
  apply Prod.ext <;> simp only [classicalDiscriminantVariationNumerator,classicalODECoefficient_apply,
    Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,
    smul_eq_mul] <;> ring

/-- Initial-value uniqueness identifies the constructed numerator with
the genuine potential derivative, without requiring distinct parameters. -/
theorem classicalDiscriminantVariationNumerator_eq (Φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalDiscriminantVariationNumerator Φ z w v t =
      (2*(w-z)) • classicalPotentialVariation Φ (classicalDiscriminantHamiltonianDirection Φ w) z v t := by
  let H := classicalDiscriminantHamiltonianDirection Φ w
  let c := 2*(w-z)
  let V := classicalPotentialVariation Φ H z v
  let R := classicalDiscriminantVariationNumerator Φ z w v
  have hc : Continuous (fun s => R s-c • V s) :=
    (continuous_classicalDiscriminantVariationNumerator Φ z w v).sub
      ((contDiff_classicalPotentialVariation Φ H z v).continuous.const_smul c)
  have he := classicalSolution_unique Φ z 0 (fun s => R s-c • V s) hc.continuousOn
    (by simp [R,V]) (by
      intro s _
      have hd := (hasDerivAt_classicalDiscriminantVariationNumerator Φ z w v s).sub
        ((hasDerivAt_classicalPotentialVariation Φ H z v s).const_smul c)
      convert! hd using 1
      apply Prod.ext <;>
        simp only [classicalODECoefficient_apply,classicalPotentialVariationSource_apply,
          Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,
          smul_eq_mul,H,c] <;>
        dsimp [R,V] <;> ring)
  have hz : classicalSolution Φ z 0 t = 0 := by
    rw [classicalSolution_eq_columns]
    simp
  have h := he t.property
  rw [hz] at h
  exact sub_eq_zero.mp h

/-- The potential derivative of the whole monodromy matrix evaluates
entrywise as the corresponding scalar potential derivative. -/
theorem fderiv_classicalMonodromy_entry (Φ H : Curve (ℂ × ℂ)) (z : ℂ) (i j : Fin 2) :
    ((fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalMonodromy Ψ z) Φ) H) i j =
      (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalMonodromy Ψ z i j) Φ) H := by
  have hf : DifferentiableAt ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalMonodromy Ψ z) Φ :=
    ((analyticOnNhd_classicalMonodromy_joint (z,Φ) (mem_univ _)).comp
      (f := fun Ψ : Curve (ℂ × ℂ) => (z,Ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hr := differentiableAt_pi.mp hf i
  have h := congrArg (fun L => L H) (fderiv_apply hr j)
  rw [fderiv_apply hf i] at h
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply] using! h.symm

/-- The actual monodromy derivative is the matrix of endpoint solution variations. -/
theorem fderiv_classicalMonodromy_eq_potentialVariations (Φ H : Curve (ℂ × ℂ)) (z : ℂ) :
    (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalMonodromy Ψ z) Φ) H =
      !![(classicalPotentialVariation Φ H z (1,0) 1).1,(classicalPotentialVariation Φ H z (0,1) 1).1;
        (classicalPotentialVariation Φ H z (1,0) 1).2,(classicalPotentialVariation Φ H z (0,1) 1).2] := by
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have hv (v : ℂ × ℂ) : DifferentiableAt ℂ
      (fun Ψ : Curve (ℂ × ℂ) => classicalSolution Ψ z v t) Φ :=
    ((analyticOnNhd_classicalSolution_joint v t (z,Φ) (mem_univ _)).comp
      (f := fun Ψ : Curve (ℂ × ℂ) => (z,Ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hfst (v : ℂ × ℂ) : (fderiv ℂ
      (fun Ψ : Curve (ℂ × ℂ) => (classicalSolution Ψ z v t).1) Φ) H =
        (classicalPotentialVariation Φ H z v t).1 := by
    rw [(hv v).hasFDerivAt.fst.fderiv,ContinuousLinearMap.comp_apply,
      fderiv_classicalSolution_potential Φ H z v t,ContinuousLinearMap.coe_fst']
  have hsnd (v : ℂ × ℂ) : (fderiv ℂ
      (fun Ψ : Curve (ℂ × ℂ) => (classicalSolution Ψ z v t).2) Φ) H =
        (classicalPotentialVariation Φ H z v t).2 := by
    rw [(hv v).hasFDerivAt.snd.fderiv,ContinuousLinearMap.comp_apply,
      fderiv_classicalSolution_potential Φ H z v t,ContinuousLinearMap.coe_snd']
  apply Matrix.ext
  intro i j
  rw [fderiv_classicalMonodromy_entry]
  fin_cases i <;> fin_cases j <;>
    simpa only [classicalMonodromy,classicalFundamentalMatrix,Matrix.of_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,t] using
      (by first | exact hfst (1,0) | exact hfst (0,1) | exact hsnd (1,0) | exact hsnd (0,1))

/-- The actual Hamiltonian monodromy variation is the commutator, with
the spectral denominator cleared. This also holds at coincident parameters. -/
theorem fderiv_classicalMonodromy_hamiltonian_commutator
    (Φ : Curve (ℂ × ℂ)) (z w : ℂ) :
    (2*(z-w)) • ((fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalMonodromy Ψ z) Φ)
      (classicalDiscriminantHamiltonianDirection Φ w)) =
        classicalMonodromy Φ z*classicalMonodromy Φ w-
          classicalMonodromy Φ w*classicalMonodromy Φ z := by
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have hv (v : ℂ × ℂ) :
      (2*(w-z)) • classicalPotentialVariation Φ (classicalDiscriminantHamiltonianDirection Φ w) z v 1 =
        classicalDiscriminantTransport Φ w 0 (classicalSolution Φ z v 1)-
          ((classicalDiscriminantTransport Φ w 0 v).1 • classicalSolution Φ z (1,0) 1+
            (classicalDiscriminantTransport Φ w 0 v).2 • classicalSolution Φ z (0,1) 1) := by
    rw [← classicalDiscriminantVariationNumerator_eq Φ z w v t]
    unfold classicalDiscriminantVariationNumerator
    rw [classicalDiscriminantTransport_endpoints,
      classicalSolution_eq_columns Φ z (classicalDiscriminantTransport Φ w 0 v) t]
  have hf₁ := congrArg Prod.fst (hv (1,0))
  have hs₁ := congrArg Prod.snd (hv (1,0))
  have hf₂ := congrArg Prod.fst (hv (0,1))
  have hs₂ := congrArg Prod.snd (hv (0,1))
  simp only [classicalDiscriminantTransport,classicalDiscriminantGradient_zero,classicalDiscriminantDiagonal_zero,
    classicalMonodromy,classicalFundamentalMatrix,Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul] at hf₁ hs₁ hf₂ hs₂
  dsimp at hf₁ hs₁ hf₂ hs₂
  rw [fderiv_classicalMonodromy_eq_potentialVariations]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply,Matrix.mul_apply,Fin.sum_univ_two,
      classicalMonodromy,classicalFundamentalMatrix] <;> dsimp
  · linear_combination (norm := (ring_nf; simp [I_sq])) -hf₁
  · linear_combination (norm := (ring_nf; simp [I_sq])) -hf₂
  · linear_combination (norm := (ring_nf; simp [I_sq])) -hs₁
  · linear_combination (norm := (ring_nf; simp [I_sq])) -hs₂

end NLS.ZakharovShabat
