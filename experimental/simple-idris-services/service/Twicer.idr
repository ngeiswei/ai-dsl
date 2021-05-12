module Twicer

import RealizedFunction
import Numeric

%default total

-- Realized twicer
public export
-- Guaranteed to produce a value divisible by 2
twicer : WFInt -> EvenNumber
twicer b = ((2 * b) ** (Even (b ** ?pr)))

public export
twicer_attrs : RealizedAttributes
twicer_attrs = MkRealizedAttributes (MkCosts 200 20 2) 0.9

public export
rlz_twicer : RealizedFunction (WFInt -> (a : WFInt ** Parity a 2)) Twicer.twicer_attrs
rlz_twicer = MkRealizedFunction twicer twicer_attrs
