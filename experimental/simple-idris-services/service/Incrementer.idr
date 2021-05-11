module Incrementer

import public RealizedFunction
import Numeric

%default total

-- Realized incrementer
-- TODO: Fix case of n = 1, which should always have proveable parity
-- public export
-- incrementer : (a : WFInt ** Parity a n) -> (b : WFInt ** OddParity b n)
-- incrementer = ?inc -- Fill with a hole until OddParity is proveable
-- -- incrementer = (+1)
public export
incrementer : WFInt -> WFInt
-- incrementer = ?inc -- Fill with a hole until OddParity is proveable
incrementer = (+1)

public export
incrementer_attrs : RealizedAttributes
incrementer_attrs = MkRealizedAttributes (MkCosts 100 10 1) 1

public export
rlz_incrementer : RealizedFunction (WFInt -> WFInt) Incrementer.incrementer_attrs
rlz_incrementer = MkRealizedFunction incrementer incrementer_attrs
