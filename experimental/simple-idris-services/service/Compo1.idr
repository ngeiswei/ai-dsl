module Compo1

import Numeric
import Incrementer
import Twicer

%default total

compo1 : WFInt -> WFInt
compo1 = incrementer . (cast . twicer)

-- -- Realized (twicer . incrementer).
-- rlz_compo1_attrs : RealizedAttributes
-- rlz_compo1_attrs = MkRealizedAttributes (MkCosts 300 30 3) 0.9
-- -- The following does not work because 301 ≠ 200+100
-- -- rlz_compo1_attrs = MkRealizedAttributes (MkCosts 301 30 3) 0.9
-- rlz_compo1 : RealizedFunction (WFInt -> Int) Compo1.rlz_compo1_attrs
-- rlz_compo1 = compose rlz_twicer rlz_incrementer
