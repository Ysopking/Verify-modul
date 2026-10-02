import YangMills.RG.FinitePiLpPointSourceRightInverse
import YangMills.RG.BalabanCMP89NeumannPrecisionThreeSpecies
import YangMills.RG.BalabanCMP89CanonicalNeumannReflectionInverseProducer
import YangMills.RG.BalabanCMP99SourceFlowFlatPrecisionScalarDictionary

namespace YangMills.RG

noncomputable section

variable {ι g : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup g] [NormedSpace ℝ g]

/-- Exact C5 final adapter: proving every literal point-source column is
sufficient for the regional right-inverse operator identity. -/
theorem c5PointSourceAdapter_smoke
    (precision imageGreen :
      FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (hpoint :
      ∀ source v,
        precision (imageGreen (singleFinitePiLp source v)) =
          singleFinitePiLp source v) :
    precision.comp imageGreen =
      ContinuousLinearMap.id ℝ (FinitePiLpField ι g) :=
  (finitePiLp_comp_eq_id_iff_pointSources precision imageGreen).2 hpoint

variable {d L depth : ℕ} [NeZero L]

/-- Source-normalization firewall: Fourier and counting coefficients are
related by the repository's exact block-weight identity; they are not
identified by hand. -/
theorem c5CoefficientBridge_smoke (a : ℝ) :
    cmp99SourceFlowFlatFullComplexA a L depth *
        cmp99SourceBlockAverageWeight
          (cmp99SourceGeneratedFullComplexBlockSide L (depth + 1)) d =
      cmp99SourceFlowFlatCountingA d a L depth *
        (cmp99SourceBlockAverageWeight
          (cmp99SourceGeneratedFullComplexBlockSide L (depth + 1)) d) ^ 2 :=
  cmp99SourceFlowFlatFullComplexA_mul_weight d L depth a

#check finitePiLp_comp_eq_id_iff_pointSources
#check cmp89SourceNeumannRegionalGaugePrecision_comp_eq_threeSpecies
#check cmp89CanonicalNeumannReflectionRepresentation_of_rightInverse
#check cmp99SourceFlowFlatFullComplexA_mul_weight

end

end YangMills.RG
