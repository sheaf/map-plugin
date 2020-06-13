{-# OPTIONS_GHC -fplugin=MapPlugin #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE TypeOperators       #-}

module Plugin.Example where

-- base
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

pass1 :: ( m ~ Insert k v s, Lookup k s ~ Nothing )
      => Dict ( Lookup k m ~ Just v )
pass1 = Dict

pass2 :: ( m ~ Delete l ( Insert k v s ), Lookup k s ~ 'Nothing, ( k == l ) ~ 'False )
      => Dict ( Lookup k m ~ Just v )
pass2 = Dict

pass3 :: ( m ~ Insert k v ( Delete k s ) )
      => Dict ( Lookup k m ~ Just v )
pass3 = Dict

pass4 :: ( m ~ Delete k s )
      => Dict ( Lookup k m ~ Nothing )
pass4 = Dict

--------------------------------------------------------------------------------
-- Should not type-check.

-- @ Could not deduce Lookup k s ~ Nothing @
fail1 :: ( m ~ Insert k v s )
      => ()
fail1 = ()

-- @ Could not deduce Lookup k m ~ Just v @
fail2 :: ( m ~ Delete l ( Insert k v s ), Lookup k s ~ 'Nothing )
      => Dict ( Lookup k m ~ Just v )
fail2 = Dict

-- @ Could not deduce Lookup k ( Insert k w s ) ~ Nothing @
fail3 :: ( m ~ Insert k v ( Insert k w s ), Lookup k s ~ 'Nothing )
      => ()
fail3 = ()
