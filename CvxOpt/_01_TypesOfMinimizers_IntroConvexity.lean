import Init.Prelude

import CvxOpt._00_IntroToOptProblems
import CvxOpt._01_TypesOfMinimizers_IntroConvexity_pre


section main

variable
    {D: Type*}
    {R: Type*}

def LocalMinimizer
    [PseudoMetricSpace D] [LE R]
    (f: D → R)
    (S: Set D)
    (x : D)
    : Prop
    := (x ∈ S) ∧ ∃ ε : NNReal, ∀ y ∈ (S ∩ Metric.ball x ε), f x ≤ f y

def StrictLocalMinimizer
    [PseudoMetricSpace D] [LT R]
    (f: D → R)
    (S: Set D)
    (x : D)
    : Prop
    := (x ∈ S) ∧ ∃ ε : NNReal, ∀ y ∈ (S ∩ Metric.ball x ε), f x < f y

def IsolatedStrictLocalMinimizer
    [PseudoMetricSpace D] [LT R] [LE R]
    (f: D → R)
    (S: Set D)
    (x : D)
    : Prop
    :=
        StrictLocalMinimizer f S x
        ∧ ∃ ε : NNReal, ∀ y : D, (LocalMinimizer f (S ∩ Metric.ball x ε) y → y = x)

end main
