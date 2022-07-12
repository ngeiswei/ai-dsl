module Descent

import OrdProofs

||| Descent algorithm, attempts to find the best candidate minimizing
||| a cost function.
|||
||| Takes in arguments:
|||
||| 1. `cnd`, an initial candidate to start the search from.
|||
||| 2. `cstfn`, a cost function that evaluates the cost of any given
||| candidate.
|||
||| 3. `nxtfn`, a search step function that given a candidate returns
||| another (supposedly better) candidate.  To do well such function
||| should take and return a search state, but for now it is
||| stateless.
|||
||| Returns a candidate that is as good as or better than `cnd`.
|||
||| For now the descent algorithm merely iteratively calls the search
||| function as long as the cost function over its output is lower.
-- NEXT: add note about well founded cost to guaranty termination
-- NEXT: Epsilon
descent_rec : Ord cost_t =>
              (cnd_t -> cost_t) -> -- Cost function
              (cnd_t -> cnd_t) ->  -- Next function to jump to the next candidate
              (cnd_t, cost_t) ->   -- Input pair of candidate and its cost
              (cnd_t, cost_t)      -- Output pair of candidate and its cost
descent_rec cstfn nxtfn (cnd, cst) =
  if nxtcst < cst then descent_rec cstfn nxtfn (nxtcnd, nxtcst)
                  else (cnd, cst)
  where
    -- Next candidate
    nxtcnd : cnd_t
    nxtcnd = nxtfn cnd
    -- Cost over next candidate
    nxtcst : cost_t
    nxtcst = cstfn nxtcnd

descent : Ord cost_t =>
          (cnd_t -> cost_t) ->  -- Cost function
          (cnd_t -> cnd_t) ->   -- Next function
          cnd_t ->              -- Input candidate
          cnd_t                 -- Output candidate
descent cstfn nxtfn cnd = fst (descent_rec cstfn nxtfn (cnd, cstfn cnd))

-- TODO: explore returning the whole trace.

-- TODO: support backtracking (trace is a tree instead of a vector)
-- (look at sorted tree).

--------------------------
-- Proofs about descent --
--------------------------

-- NEXT.0: Use delta as stopping point

-- NEXT.-1: Global vs local (or compare locals)


||| Proof that the output candidate of descent_rec has a cost less
||| than or equal to the cost of the input candidate.
|||
||| The simplicity of the proof of descent_rec_le is due to the case
||| base approach which allows Idris to partially evaluate descent_rec.
||| This partial evaluation is then reflected inside the target
||| theorem.  For instance if
|||
||| ((cstfn (nxtfn cnd)) < cst) = False
|||
||| the target theorem
|||
||| (snd (descent_rec cstfn nxtfn cndcst)) <= (snd cndcst) = True
|||
||| gets reduced to
|||
||| (snd cndcst) <= (snd cndcst)
|||
||| which merely requires the axiom of reflexivity of <=.
|||
||| Likewise if
|||
||| (cstfn (nxtfn cnd) < cst) = True
|||
||| the target theorem
|||
||| (snd (descent_rec cstfn nxtfn (cnd, cst))) <= (snd (cnd, cst)) = True
|||
||| gets reduced to
|||
||| (snd (descent_rec cstfn nxtfn (nxtfn cnd, cstfn (nxtfn cnd)))) <= cst = True
|||
||| which then merely requires to apply the transitivity axiom of <=
||| over the recursive theorem
|||
||| (snd (descent_rec cstfn nxtfn (nxtfn cnd, cstfn (nxtfn cnd)))) <= cstfn (nxtfn cnd) = True
|||
||| and
|||
||| (cstfn (nxtfn cnd) <= cst) = True
|||
||| which is obtained as the reflexive closure of <= over the
||| hypothesis.
descent_rec_le : Ord cost_t =>
                     (cstfn : cnd_t -> cost_t) ->  -- Cost function
                     (nxtfn : cnd_t -> cnd_t) ->   -- Next function
                     (cndcst : (cnd_t, cost_t)) -> -- Input pair of candidate and its cost
                     (snd (descent_rec cstfn nxtfn cndcst)) <= (snd cndcst) = True -- Theorem
descent_rec_le cstfn nxtfn (cnd, cst) with ((cstfn (nxtfn cnd)) < cst) proof eq
  _ | True = let des_le_nxtcst = descent_rec_le cstfn nxtfn (nxtfn cnd, (cstfn (nxtfn cnd)))
                 nxtcst_le_cst = le_reflexive_closure_lt (Left eq)
              in (le_transitive des_le_nxtcst nxtcst_le_cst)
  _ | False = le_reflexive

||| Proof that
|||
||| cstfn (descent cstfn nxtfn cnd) = snd (descent_rec cstfn nxtfn (cnd, cstfn cnd))
|||
||| This is used by descent_le to get passed
|||
|||        snd (descent_rec cstfn nxtfn (cnd, cstfn cnd)) <= cstfn cnd = True
||| ->
||| cstfn (fst (descent_rec cstfn nxtfn (cnd, cstfn cnd))) <= cstfn cnd = True
cd_eq_sdr : Ord cost_t =>
            (cstfn : cnd_t -> cost_t) ->  -- Cost function
            (nxtfn : cnd_t -> cnd_t) ->   -- Next function
            (cnd : cnd_t) ->              -- Input candidate
            (cstfn (descent cstfn nxtfn cnd)) = snd (descent_rec cstfn nxtfn (cnd, cstfn cnd))
cd_eq_sdr cstfn nxtfn cnd = believe_me () -- NEXT.1

||| Proof that the output candidate of descent has a cost less than or
||| equal to the cost of the input candidate.
|||
||| The target theorem
|||
||| (cstfn (descent cstfn nxtfn cnd)) <= (cstfn cnd) = True
|||
||| gets reduced to
|||
||| (cstfn (fst (descent_rec cstfn nxtfn (cnd, cstfn cnd)))) <= (cstfn cnd) = True
|||
||| by virtue of the definition of descent.
descent_le : Ord cost_t =>
             (cstfn : cnd_t -> cost_t) ->                            -- Cost function
             (nxtfn : cnd_t -> cnd_t) ->                             -- Next function
             (cnd : cnd_t) ->                                        -- Input candidate
             (cstfn (descent cstfn nxtfn cnd)) <= (cstfn cnd) = True -- Theorem
descent_le cstfn nxtfn cnd = rewrite (cd_eq_sdr cstfn nxtfn cnd)
                                  in (descent_rec_le cstfn nxtfn (cnd, cstfn cnd))
