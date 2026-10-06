import YangMills.RG.FinitePiLpPointSourceRightInverse
import YangMills.RG.BalabanCMP89NeumannMassReflection
import YangMills.RG.BalabanCMP89NeumannPrecisionThreeSpecies

/-!
# R3 probe: point-source three-species reduction

Compiler retry: exact parent graph persisted before wrapper seal.

This isolated verification probe keeps the exact pinned upstream source and
rebuilds only the failed local theorem descendant from Run 37039688079.
It does not assert FULLG-FUND, RI-LAP-IMG, RI-Q, C5-G0, or global Yang-Mills.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

set_option maxHeartbeats 2000000 in
 theorem cmp89SourceNeumannRegionalGaugePrecision_comp_reflection_eq_id_iff_pointSource_threeSpecies_r3
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {m : Fin d → ℤ}
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (Qprime : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ] F)
    (spacing mass a : ℝ)
    (siteEquiv : CMP89SourceNeumannIntegerRectanglePoint m ≃
      ActiveGaugeRegion.Site Omega)
    (fullGreen : (Fin d → ℤ) → (Fin d → ℤ) → ℝ) :
    (cmp89SourceNeumannRegionalGaugePrecision
        Omega rho U Qprime spacing mass a).comp
          (cmp89NeumannScalarReflectionOperator
            (g := SUNLieCoord Nc) siteEquiv fullGreen) =
        ContinuousLinearMap.id ℝ
          (ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) ↔
      ∀ source v,
        cmp89SourceNeumannRegionalLaplacian Omega rho U spacing
              (cmp89NeumannScalarReflectionOperator
                (g := SUNLieCoord Nc) siteEquiv fullGreen
                (singleFinitePiLp source v)) +
            cmp89NeumannScalarReflectionOperator
              (g := SUNLieCoord Nc) siteEquiv
              (fun y z => mass ^ 2 * fullGreen y z)
              (singleFinitePiLp source v) +
            (a • (Qprime.adjoint.comp Qprime))
              (cmp89NeumannScalarReflectionOperator
                (g := SUNLieCoord Nc) siteEquiv fullGreen
                (singleFinitePiLp source v)) =
          singleFinitePiLp source v := by
  let G := cmp89NeumannScalarReflectionOperator
    (g := SUNLieCoord Nc) siteEquiv fullGreen

  have hthree :
      (cmp89SourceNeumannRegionalGaugePrecision
          Omega rho U Qprime spacing mass a).comp G =
        (cmp89SourceNeumannRegionalLaplacian
          Omega rho U spacing).comp G +
        cmp89NeumannScalarReflectionOperator
          (g := SUNLieCoord Nc) siteEquiv
          (fun y z => mass ^ 2 * fullGreen y z) +
        ((a • (Qprime.adjoint.comp Qprime)).comp G) := by
    have h :=
      cmp89SourceNeumannRegionalGaugePrecision_comp_eq_threeSpecies
        Omega rho U Qprime spacing mass a G
    have hmass :=
      mass_sq_comp_cmp89NeumannScalarReflectionOperator
        (g := SUNLieCoord Nc) mass siteEquiv fullGreen
    rw [hmass] at h
    exact h

  constructor
  · intro h source v
    have hpoint :=
      (finitePiLp_comp_eq_id_iff_pointSources
        (cmp89SourceNeumannRegionalGaugePrecision
          Omega rho U Qprime spacing mass a) G).mp h source v
    have hsplit := congrArg
      (fun T : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
          ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) =>
        T (singleFinitePiLp source v)) hthree
    calc
      cmp89SourceNeumannRegionalLaplacian Omega rho U spacing
              (G (singleFinitePiLp source v)) +
            cmp89NeumannScalarReflectionOperator
              (g := SUNLieCoord Nc) siteEquiv
              (fun y z => mass ^ 2 * fullGreen y z)
              (singleFinitePiLp source v) +
            (a • (Qprime.adjoint.comp Qprime))
              (G (singleFinitePiLp source v)) =
          cmp89SourceNeumannRegionalGaugePrecision
            Omega rho U Qprime spacing mass a
            (G (singleFinitePiLp source v)) := by
              simpa only [ContinuousLinearMap.comp_apply,
                ContinuousLinearMap.add_apply] using hsplit.symm
      _ = singleFinitePiLp source v := hpoint
  · intro h
    apply (finitePiLp_comp_eq_id_iff_pointSources
      (cmp89SourceNeumannRegionalGaugePrecision
        Omega rho U Qprime spacing mass a) G).mpr
    intro source v
    have hsplit := congrArg
      (fun T : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
          ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) =>
        T (singleFinitePiLp source v)) hthree
    calc
      cmp89SourceNeumannRegionalGaugePrecision
            Omega rho U Qprime spacing mass a
            (G (singleFinitePiLp source v)) =
          cmp89SourceNeumannRegionalLaplacian Omega rho U spacing
              (G (singleFinitePiLp source v)) +
            cmp89NeumannScalarReflectionOperator
              (g := SUNLieCoord Nc) siteEquiv
              (fun y z => mass ^ 2 * fullGreen y z)
              (singleFinitePiLp source v) +
            (a • (Qprime.adjoint.comp Qprime))
              (G (singleFinitePiLp source v)) := by
              simpa only [ContinuousLinearMap.comp_apply,
                ContinuousLinearMap.add_apply] using hsplit
      _ = singleFinitePiLp source v := h source v

end

end YangMills.RG

#print axioms YangMills.RG.cmp89SourceNeumannRegionalGaugePrecision_comp_reflection_eq_id_iff_pointSource_threeSpecies_r3
