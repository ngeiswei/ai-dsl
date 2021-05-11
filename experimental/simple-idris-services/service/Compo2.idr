module Compo2

import Numeric
import Incrementer
import Twicer
import Halfer

%default total

compo2 : EvenNumber -> WFInt
compo2 = incrementer . ((cast . twicer) . halfer)

-- -- Realized (incrementer . twicer . halfer).
-- rlz_compo2_attrs : RealizedAttributes
-- rlz_compo2_attrs = MkRealizedAttributes (MkCosts 600 60 6) 0.8
-- -- The following does not work because 601 ≠ 300+200+100
-- -- rlz_compo2_attrs = MkRealizedAttributes (MkCosts 601 60 6) 0.8
-- rlz_compo2 : RealizedFunction (Int -> Int) Compo2.rlz_compo2_attrs
-- rlz_compo2 = (compose rlz_incrementer (compose rlz_twicer rlz_halfer))
