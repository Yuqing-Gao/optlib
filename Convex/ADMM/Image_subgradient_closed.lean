import Convex.Function.Proximal
import Mathlib.Topology.MetricSpace.Sequences

noncomputable section

open Set InnerProductSpace Topology Filter

-- The image of the subgradient is closed
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (f : E → ℝ )(x' : E)( g' : E)

-- 参考书P64 定理2.19
theorem Image_subgradient_closed
(lscf: LowerSemicontinuous f)(cf : ConvexOn ℝ univ f)
(x : ℕ → E )(x_converage: Tendsto x atTop (𝓝 x'))
(g : ℕ → E )(g_coverage : Tendsto g atTop (𝓝 g'))
(nonempty :  ∀ n ,(g n) ∈ SubderivAt f (x n))
: g' ∈ SubderivAt f x' := sorry
