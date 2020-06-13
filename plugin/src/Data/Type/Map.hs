{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}

module Data.Type.Map where

--------------------------------------------------------------------------------
-- Key/value pair type.

infixr 4 :->
data k :-> v = k :-> v

type Key :: k :-> v -> k
type family Key kv where
  Key ( k ':-> _ ) = k

type Value :: k :-> v -> v
type family Value kv where
  Value ( _ ':-> v ) = v

--------------------------------------------------------------------------------
-- Map, represented as a sorted list of key/value pairs.

data Map k v = FromList [ k :-> v ]

type Lookup :: k -> Map k v -> Maybe v
type family Lookup k kvs where

type Insert :: k -> v -> Map k v -> Map k v
type family Insert k v kvs where

type Union :: Map k v -> Map k v -> Map k v
type family Union as bs where

type Delete :: k -> Map k v -> Map k v
type family Delete k kvs where

type Difference :: Map k v -> Map k v -> Map k v
type family Difference as bs where
