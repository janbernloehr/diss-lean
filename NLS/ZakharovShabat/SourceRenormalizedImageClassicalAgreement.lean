import NLS.ZakharovShabat.SourceHamiltonianRenormalizedImageFlow
import NLS.ZakharovShabat.SourceHamiltonianRenormalizedFlowExponent
import NLS.ZakharovShabat.ClassicalRenormalizedNLSFiniteGap

/-! # Classical agreement of the actual renormalized image flow

Hilbert source trajectories included into p ≥ 2 stay in the actual
Birkhoff image for all times and coincide with the image-inverse flow.
Finite-gap sources have the same Hilbert model and physical representative,
so their actual classical Fourier integrals identify the local source map.
-/
noncomputable section
open Set NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P V B X : Set (CoeffPair p)}
variable {s t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₂ P₂ V₂ B₂ X₂ : Set (CoeffPair 2)}
variable {s₂ t₂ : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The included Hilbert trajectory has precisely the actual larger-exponent phase coordinates. -/
theorem complex_map_included_hamiltonianRenormalizedFlow
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (H : SourceAbelianMomentAtlas (by simp) (by norm_num) W₂ s₂)
    (hs₂ : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P₂ s₂)
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₂ B₂ X₂ t₂)
    (h2p : 2 ≤ p) (φ : realTypeSourceSubmodule 2) (time : ℝ) :
    sourceComplexBirkhoffMap hp hp1 t
      (realTypeSourceExponentInclusion h2p (H.hamiltonianRenormalizedSourceFlow E le_rfl φ time)).val =
      A.renormalizedPhaseTrajectory t (realTypeSourceExponentInclusion h2p φ) (-time) := by
  let L := (Coeff.exponentInclusion h2p).prodMap (Coeff.exponentInclusion h2p)
  have hz := E.complex_map_exponent D h2p φ
  have hphase : L (Birkhoff.hamiltonianPhaseFlow (H.phaseFrequency φ) time
      (sourceComplexBirkhoffMap (by simp) (by norm_num) t₂ φ.val)) =
      Birkhoff.hamiltonianPhaseFlow (A.phaseFrequency (realTypeSourceExponentInclusion h2p φ)) time
        (sourceComplexBirkhoffMap hp hp1 t (realTypeSourceExponentInclusion h2p φ).val) := by
    apply Prod.ext
    · ext n
      change Complex.exp _ * _ = Complex.exp _ * _
      dsimp only
      rw [← H.phaseFrequency_exponent A hs₂ hs h2p φ n]
      congr 1
      exact congrArg (fun z : Coeff p × Coeff p => z.1 n) hz
    · ext n
      change (Birkhoff.hamiltonianPhaseFlow (H.phaseFrequency φ) time
        (sourceComplexBirkhoffMap (by simp) (by norm_num) t₂ φ.val)).2 n = _
      simp only [Birkhoff.hamiltonianPhaseFlow_snd]
      rw [← H.phaseFrequency_exponent A hs₂ hs h2p φ n]
      congr 1
      exact congrArg (fun z : Coeff p × Coeff p => z.2 n) hz
  exact (E.complex_map_exponent D h2p _).symm.trans
    ((congrArg L (H.complex_map_hamiltonianRenormalizedSourceFlow E le_rfl φ time)).trans hphase)

/-- Every included Hilbert trajectory is admissible, even when the larger
exponent's Birkhoff map is only known to be an embedding. -/
theorem hilbert_inclusion_mem_renormalizedImageDomain
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (H : SourceAbelianMomentAtlas (by simp) (by norm_num) W₂ s₂)
    (hs₂ : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P₂ s₂)
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₂ B₂ X₂ t₂)
    (h2p : 2 ≤ p) (φ : realTypeSourceSubmodule 2) (time : ℝ) :
    (-time,realTypeSourceExponentInclusion h2p φ) ∈ A.renormalizedImageDomain t := by
  have he := congrArg (Birkhoff.decodeReal (p := p))
    (A.complex_map_included_hamiltonianRenormalizedFlow hs D H hs₂ E h2p φ time)
  let ψ : realTypeSourceSubmodule p :=
    realTypeSourceExponentInclusion h2p (H.hamiltonianRenormalizedSourceFlow E le_rfl φ time)
  have hd : Birkhoff.decodeReal (sourceComplexBirkhoffMap hp hp1 t ψ.val) =
      sourceRealBirkhoffMap hp hp1 t ψ :=
    (congrArg (Birkhoff.decodeReal (p := p)) (D.encode_real_map ψ).symm).trans
      (Birkhoff.decodeReal_encodeReal _)
  exact ⟨ψ,hd.symm.trans he⟩

/-- Evolution and inclusion commute for every Hilbert initial source at p ≥ 2. -/
theorem hamiltonianRenormalizedImageFlow_hilbert_inclusion
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (H : SourceAbelianMomentAtlas (by simp) (by norm_num) W₂ s₂)
    (hs₂ : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P₂ s₂)
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₂ B₂ X₂ t₂)
    (h2p : 2 ≤ p) (φ : realTypeSourceSubmodule 2) (time : ℝ) :
    A.hamiltonianRenormalizedImageFlow D (realTypeSourceExponentInclusion h2p φ) time =
      realTypeSourceExponentInclusion h2p (H.hamiltonianRenormalizedSourceFlow E le_rfl φ time) := by
  have he := congrArg (Birkhoff.decodeReal (p := p))
    (A.complex_map_included_hamiltonianRenormalizedFlow hs D H hs₂ E h2p φ time)
  let ψ : realTypeSourceSubmodule p :=
    realTypeSourceExponentInclusion h2p (H.hamiltonianRenormalizedSourceFlow E le_rfl φ time)
  have hd : Birkhoff.decodeReal (sourceComplexBirkhoffMap hp hp1 t ψ.val) =
      sourceRealBirkhoffMap hp hp1 t ψ :=
    (congrArg (Birkhoff.decodeReal (p := p)) (D.encode_real_map ψ).symm).trans
      (Birkhoff.decodeReal_encodeReal _)
  have he' := hd.symm.trans he
  unfold hamiltonianRenormalizedImageFlow renormalizedImageFlow
  rw [← he',D.realImageInverse_real_map]

/-- Actual finite-gap initial sources are admissible for all physical times above the Hilbert exponent. -/
theorem finiteGap_mem_renormalizedImageDomain
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t) (h2p : 2 ≤ p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (time : ℝ) :
    (-time,φ) ∈ A.renormalizedImageDomain t := by
  obtain ⟨W₂,P₂,_,_,_,_,s₂,hs₂,⟨H⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas (p := 2) (by simp) (by norm_num)
  obtain ⟨V₂,B₂,X₂,t₂,E⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  simpa only [sourceFiniteGapHilbertModel_inclusion] using!
    A.hilbert_inclusion_mem_renormalizedImageDomain hs D H hs₂.toSourcePsiIsolatingComplexExtension E h2p
      (sourceFiniteGapHilbertModel hp hp1 φ hf) time

/-- The actual image flow agrees with the Fourier integrals of the unique
classical renormalized trajectory of every finite-gap source at p ≥ 2. -/
theorem hamiltonianRenormalizedImageFlow_fst_eq_classical
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t) (h2p : 2 ≤ p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (time : ℝ) (n : ℤ) :
    (A.hamiltonianRenormalizedImageFlow D φ time).val.fst n =
      periodOneCoefficient (fun x : ℝ => sourceFiniteGapClassicalRenormalizedTrajectory hp hp1 φ hf time
        (x : AddCircle (2 : ℝ))) n := by
  obtain ⟨W₂,P₂,_,_,_,_,s₂,hs₂,⟨H⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas (p := 2) (by simp) (by norm_num)
  obtain ⟨V₂,B₂,X₂,t₂,E⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  have hi := A.hamiltonianRenormalizedImageFlow_hilbert_inclusion hs D H
    hs₂.toSourcePsiIsolatingComplexExtension E h2p (sourceFiniteGapHilbertModel hp hp1 φ hf) time
  rw [sourceFiniteGapHilbertModel_inclusion] at hi
  have hc := H.periodOneCoefficient_classicalRenormalizedNLS_eq_hamiltonianFlow
    hs₂.toSourcePsiIsolatingComplexExtension E hp hp1 φ hf
    (sourceFiniteGapClassicalRenormalizedTrajectory hp hp1 φ hf)
    (sourceFiniteGapClassicalRenormalizedTrajectory_spec hp hp1 φ hf).1
    (sourceFiniteGapClassicalRenormalizedTrajectory_spec hp hp1 φ hf).2 time n
  exact (congrArg (fun ξ : realTypeSourceSubmodule p => ξ.val.fst n) hi).trans hc.symm

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
