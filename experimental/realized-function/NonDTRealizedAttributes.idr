-- Prototype of RealizedAttributes as described in
-- https://blog.singularitynet.io/ai-dsl-toward-a-general-purpose-description-language-for-ai-agents-21459f691b9e
-- except that the data structure is not dependently typed.

module NonDTRealizedAttributes

public export
CostT : Type
CostT = Double

public export
record Costs where
  constructor MkCosts
  financial, temporal, computational : CostT

public export
Quality : Type
Quality = Double

public export
record NonDTRealizedAttributes where
  constructor MkNonDTRealizedAttributes
  costs : Costs
  quality : Quality

-- Add costs
public export
add_costs : Costs -> Costs -> Costs
add_costs x y = MkCosts (x.financial + y.financial)
                        (x.temporal + y.temporal)
                        (x.computational + y.computational)

-- Add costs, minimum quality
public export
add_costs_min_quality : NonDTRealizedAttributes ->
                        NonDTRealizedAttributes ->
                        NonDTRealizedAttributes
add_costs_min_quality f_attrs g_attrs = fg_attrs where
  fg_attrs : NonDTRealizedAttributes
  fg_attrs = MkNonDTRealizedAttributes (add_costs f_attrs.costs g_attrs.costs)
                                       (min f_attrs.quality g_attrs.quality)
