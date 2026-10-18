-- | The heap references used by suspended goal plans. Compilation keeps
-- slot offsets for cheap execution; collection can detach the surviving
-- plans from their activation block by turning those offsets into words.
-- Predicate references and immutable clause plans are never traversed or
-- changed: a future clause call allocates its own activation.
module Infera.Core.Liveness
  ( visitPattern,
    visitGoals,
    relocatePattern,
    relocateGoals,
  )
where

import Infera.Core.Compile
import Infera.Core.Store (Word', refWord)

visitPattern :: (Word' -> IO ()) -> Int -> Pattern -> IO ()
visitPattern visit base pattern = case pattern of
  PSlot slot -> visit (refWord (base + slot))
  PFirst slot -> visit (refWord (base + slot))
  PWord word -> visit word
  PStruct _ children -> mapM_ (visitPattern visit base) children
  PArith _ _ children -> mapM_ (visitPattern visit base) children

visitGoals :: (Word' -> IO ()) -> Int -> [Goal] -> IO ()
visitGoals visit base = mapM_ goal
  where
    pattern = visitPattern visit base
    patterns = mapM_ pattern
    goals = visitGoals visit base
    expr expression = case expression of
      EPat p -> pattern p
      EOp _ children -> mapM_ expr children
      EImm _ -> pure ()
      EBig _ -> pure ()
      EFlt _ -> pure ()
    goal g = case g of
      GCall _ ps _ -> patterns ps
      GTabled _ ps -> patterns ps
      GCallFacts _ ps -> patterns ps
      GAssert p -> pattern p
      GRetract p -> pattern p
      GRetractAll p -> pattern p
      GMinimize p inner -> pattern p >> goals inner
      GCallDyn _ p ps -> pattern p >> patterns ps
      GAnd inner -> goals inner
      GUnify a b -> pattern a >> pattern b
      GEquiv a b -> pattern a >> pattern b
      GNeq a b -> pattern a >> pattern b
      GIs p e -> pattern p >> expr e
      GCmp _ a b -> expr a >> expr b
      GTrue -> pure ()
      GFail -> pure ()
      GCut -> pure ()
      GOr a b -> goals a >> goals b
      GIf condition yes no -> goals condition >> goals yes >> maybe (pure ()) goals no
      GNot inner -> goals inner
      GOnce inner -> goals inner
      GFindAll template inner target -> pattern template >> goals inner >> pattern target
      GCheck _ p -> pattern p
      GWrite _ p -> pattern p
      GNl -> pure ()
      GError _ -> pure ()
      GLeaf _ ps -> patterns ps
      GPhrase a b -> pattern a >> pattern b
      GPhraseFile a b -> pattern a >> pattern b
      GEmit p -> pattern p
      GEmitText p -> pattern p
      GUnsupported _ -> pure ()

-- | Capture a slot's cell, without dereferencing it. A later binding or
-- trail unwind must remain visible through exactly the same reference.
-- PFirst is confined to clause heads by the compiler; suspended goal
-- plans use PSlot. Treating it as a reference here is conservative for a
-- future plan producer that uses it only as a term operand.
relocatePattern :: (Word' -> IO Word') -> Int -> Pattern -> IO Pattern
relocatePattern relocate base pattern = case pattern of
  PSlot slot -> PWord <$> relocate (refWord (base + slot))
  PFirst slot -> PWord <$> relocate (refWord (base + slot))
  PWord word -> PWord <$> relocate word
  PStruct functor children -> PStruct functor <$> mapM (relocatePattern relocate base) children
  PArith functor op children -> PArith functor op <$> mapM (relocatePattern relocate base) children

relocateGoals :: (Word' -> IO Word') -> Int -> [Goal] -> IO [Goal]
relocateGoals relocate base = mapM goal
  where
    pattern = relocatePattern relocate base
    patterns = mapM pattern
    goals = relocateGoals relocate base
    expr expression = case expression of
      EPat p -> EPat <$> pattern p
      EOp op children -> EOp op <$> mapM expr children
      EImm n -> pure (EImm n)
      EBig n -> pure (EBig n)
      EFlt n -> pure (EFlt n)
    goal g = case g of
      GCall predicate ps trust -> (\ps' -> GCall predicate ps' trust) <$> patterns ps
      GTabled predicate ps -> GTabled predicate <$> patterns ps
      GCallFacts key ps -> GCallFacts key <$> patterns ps
      GAssert p -> GAssert <$> pattern p
      GRetract p -> GRetract <$> pattern p
      GRetractAll p -> GRetractAll <$> pattern p
      GMinimize p inner -> GMinimize <$> pattern p <*> goals inner
      GCallDyn variable p ps -> GCallDyn variable <$> pattern p <*> patterns ps
      GAnd inner -> GAnd <$> goals inner
      GUnify a b -> GUnify <$> pattern a <*> pattern b
      GEquiv a b -> GEquiv <$> pattern a <*> pattern b
      GNeq a b -> GNeq <$> pattern a <*> pattern b
      GIs p e -> GIs <$> pattern p <*> expr e
      GCmp op a b -> GCmp op <$> expr a <*> expr b
      GTrue -> pure GTrue
      GFail -> pure GFail
      GCut -> pure GCut
      GOr a b -> GOr <$> goals a <*> goals b
      GIf condition yes no -> GIf <$> goals condition <*> goals yes <*> traverse goals no
      GNot inner -> GNot <$> goals inner
      GOnce inner -> GOnce <$> goals inner
      GFindAll template inner target -> GFindAll <$> pattern template <*> goals inner <*> pattern target
      GCheck check p -> GCheck check <$> pattern p
      GWrite newline p -> GWrite newline <$> pattern p
      GNl -> pure GNl
      GError err -> pure (GError err)
      GLeaf name ps -> GLeaf name <$> patterns ps
      GPhrase a b -> GPhrase <$> pattern a <*> pattern b
      GPhraseFile a b -> GPhraseFile <$> pattern a <*> pattern b
      GEmit p -> GEmit <$> pattern p
      GEmitText p -> GEmitText <$> pattern p
      GUnsupported term -> pure (GUnsupported term)
