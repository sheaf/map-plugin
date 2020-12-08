{-# OPTIONS_GHC -fplugin=MapPlugin #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE TypeOperators       #-}

module Plugin.Example where

-- base
import Data.Proxy
  ( Proxy )
import Data.Type.Equality
  ( type (==) )

-- Plugin
import Data.Type.Map
  ( Insert, Delete, Lookup )

--------------------------------------------------------------------------------

data Dict ct where
  Dict :: ct => Dict ct

--------------------------------------------------------------------------------
-- Should type-check.

-- @ Lookup k ( Insert k v m ) = Just v @
pass1 :: ( s ~ Insert k v m, Lookup k m ~ Nothing )
      => Proxy k -> Proxy v -> Proxy m -> Proxy s
      -> Dict ( Lookup k s ~ Just v )
pass1 _ _ _ _ = Dict

-- @ Lookup k ( Delete l m ) = Lookup k m @ if @ l /= k@.
pass2 :: ( s ~ Delete l m, ( k == l ) ~ 'False )
      => Proxy k -> Proxy l -> Proxy v -> Proxy s -> Proxy m
      -> Dict ( Lookup k s ~ Lookup k m )
pass2 _ _ _ _ _ = Dict

-- @ Lookup k ( Delete k m ) = Nothing @.
pass3 :: ( s ~ Delete k m )
      => Proxy k -> Proxy v -> Proxy s -> Proxy m
      -> Dict ( Lookup k s ~ Nothing )
pass3 _ _ _ _ = Dict

-- @ Insert k v ( Delete k m ) = m @ when @ Lookup k m = Just v @.
pass4 :: ( s ~ Delete k m, Lookup k m ~ Just v )
      => Proxy k -> Proxy v -> Proxy s -> Proxy m
      -> Dict ( m ~ Insert k v s )
pass4 _ _ _ _ = Dict

-- @ Delete k ( Insert k v m ) = m @.
pass5 :: ( s ~ Insert k v m, Lookup k m ~ Nothing )
      => Proxy k -> Proxy v -> Proxy s -> Proxy m
      -> Dict ( m ~ Delete k s )
pass5 _ _ _ _ = Dict

-- @ Delete k m = m @ when @ Lookup k m = Nothing @.
pass6 :: ( Lookup k m ~ Nothing )
      => Proxy k -> Proxy v -> Proxy m
      -> Dict ( m ~ Delete k m )
pass6 _ _ _ = Dict

--------------------------------------------------------------------------------
-- Should not type-check.

-- 'fail1', 'fail3' and 'fail4' unexpectedly typecheck
-- as the plugin is not even invoked
-- (lack of constrained type families)

-- @ Could not deduce Lookup k s ~ Nothing @
fail1 :: ( m ~ Insert k v s )
      => Proxy k -> Proxy v -> Proxy s -> Proxy m
      -> ()
fail1 _ _ _ _ = ()

-- @ Could not deduce Lookup k m ~ Just v @
fail2 :: ( m ~ Delete l ( Insert k v s ), Lookup k s ~ 'Nothing )
      => Proxy k -> Proxy l -> Proxy v -> Proxy s -> Proxy m
      -> Dict ( Lookup k m ~ Just v )
fail2 _ _ _ _ _ = Dict

-- @ Could not deduce Lookup k ( Insert k w s ) ~ Nothing @
fail3 :: ( m ~ Insert k v ( Insert k w s ), Lookup k s ~ 'Nothing )
      => Proxy k -> Proxy v -> Proxy w -> Proxy s -> Proxy m
      -> ()
fail3 _ _ _ _ _ = ()

-- @ Occurs check @
fail4 :: ( m1 ~ Insert k1 v1 m2, m2 ~ Insert k2 v2 m1, ( k1 == k2 ) ~ False )
      => Proxy k1 -> Proxy k2 -> Proxy v1 -> Proxy v2 -> Proxy m1 -> Proxy m2
      -> ()
fail4 _ _ _ _ _ _ = ()
