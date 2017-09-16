open import Prelude
open import Builtin.Reflection
open import Tactic.Reflection

open import Control.Monad.State

module Elaboration.Monad where

-- -----------------------------------------------------------------------------
-- The Elaboration Monad API
-- -----------------------------------------------------------------------------

-- the Elaboration state holds the goal type, the
-- current context and the partial term that is being
-- constructed
record ElabState : Set where
  constructor ElabS
  field
    goal : Type
    ctx  : List (Arg Type)
    term : Term

open ElabState

-- the Elaboration monad ElabM is a state transformer
-- holding a ElabState over TC
ElabM = StateT ElabState TC

macro
  -- the macro that emulates Idris %runElab
  %runElabM : ElabM ⊤ → Term → TC ⊤
  %runElabM e h = do t  ← inferType h
                 -| c  ← getContext
                 -| st ← runStateT e (ElabS t (reverse c) h)
                 -| return tt

-- introduce one variable in case the goal to solve
-- is a function type (pi constructor)
intro : ElabM ⊤
runStateT intro (ElabS g ctx t) with g
... | pi a (Abs.abs s t₁) =
  inContext (ctx ++ [ a ]) (do m  ← newMeta t₁
                            -| (unify t (lam (getVisibility a) (Abs.abs "" m)))
                            ~| return (tt , ElabS t₁ (ctx ++ [ a ]) m))
... | _ = typeError (strErr "Can't ′intro′ a non function type ′" ∷
                     termErr g ∷ strErr "′." ∷ [])

-- fill the current goal with the given Term
fill : Term → ElabM ⊤
runStateT (fill t) (ElabS goal ctx term) =
  inContext ctx (do unify term t
                 ~| return (tt , (ElabS goal ctx t)))

-- debug in the Elaboration monad
debug : ∀ {a : Set} → ElabM a
runStateT debug (ElabS g ctx t) =
  inContext ctx (do c ← quoteTC ctx >>= normalise
                 -| typeError (strErr "Goal: "    ∷ termErr g ∷ newLine ∷
                               strErr "Context: " ∷ termErr c ∷ newLine ∷
                               strErr "Term: "    ∷ termErr t ∷ []))
    where
      newLine = strErr "\n"

-- the tactic that always succeds
success : ElabM ⊤
success = return tt

-- the tactic that fails with a given message
fail : String → ElabM ⊤
runStateT (fail str) s = typeError [ strErr str  ]

-- try the first tactic, if fails try the second one
try : ∀ {a} → ElabM a → ElabM a → ElabM a
runStateT (try e1 e2) s = catchTC (runStateT e1 s) (runStateT e2 s)

-- -----------------------------------------------------------------------------
-- Some example `tactics` in ElabM
-- -----------------------------------------------------------------------------

-- introduce as many variables as possible
-- to make Agda's termination checker happy we introduce
-- at most 100 (who will dare to write a function with 100
-- arguments?)
intros : ElabM ⊤
intros = introsN 100
  where
    introsN : Nat → ElabM ⊤
    introsN 0       = fail "`intros` exhausted"
    introsN (suc n) = try (intro >> introsN n) success

return0 : ElabM ⊤
return0 = intros
  ~| fill (lit (nat (0)))

mkId : ElabM ⊤
mkId = do intro
       ~| fill (var 0 [])

-- -----------------------------------------------------------------------------
-- Some example programs
-- -----------------------------------------------------------------------------

idNat : Nat → Nat
idNat = %runElabM mkId

idString : String → String → String
idString = %runElabM (intro >> mkId)

mkConstE : ElabM ⊤
mkConstE = do intro
           ~| intro
           ~| fill (var 1 [])

constNat : Nat → Nat → Nat
constNat = %runElabM mkConstE

nat0 : Nat
nat0 = %runElabM return0

nat1 : Nat → Nat → Nat → Nat
nat1 = %runElabM return0

nat2 : Nat
nat2 = (%runElabM mkId) 4
