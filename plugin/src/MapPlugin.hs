{-# LANGUAGE BlockArguments     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE MagicHash          #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE TupleSections      #-}

{-# LANGUAGE TypeApplications   #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module MapPlugin ( plugin ) where

-- base
import Control.Arrow
    ( (***) )
import Control.Monad
    ( join )
import Data.Coerce
    ( coerce )
import Data.Either
    ( partitionEithers )
import Data.Foldable
    ( toList )
import Data.Maybe
    ( catMaybes, mapMaybe )
import Data.Monoid
    ( Ap(..) )
import Data.Semigroup
    ( First(..) )
import GHC.Exts
    ( Int(..), dataToTag# )

-- containers
import Data.Map.Strict
    ( Map )
import qualified Data.Map.Strict
  as Map
    ( foldMapWithKey, fromListWith, lookup
    , mapMaybeWithKey, unionWith
    )
import Data.Set
    ( Set )
import qualified Data.Set
  as Set
    ( empty, fromList, insert
    , isSubsetOf, map, singleton, union
    )

-- ghc
import qualified GHC
    ( Module, mkModuleName )
import qualified GHC.Builtin.Types
  as GHC
    ( promotedFalseDataCon, promotedTrueDataCon
    , promotedNothingDataCon, promotedJustDataCon
    )
{-
import qualified GHC.Builtin.Types.Prim
  as GHC
    ( eqPrimTyCon )
-}
import qualified GHC.Core
  as GHC
    ( Expr(Coercion) )
import qualified GHC.Core.Coercion
  as GHC
    ( Coercion, mkUnivCo, mkPrimEqPredRole )
{-
import qualified GHC.Core.DataCon
  as GHC
    ( promoteDataCon )
-}
import qualified GHC.Core.Predicate
  as GHC
    ( Pred(..), classifyPredType
    , EqRel(..)
    )
import qualified GHC.Core.TyCo.Rep
  as GHC
    ( Type(..)
    , UnivCoProvenance(..)
    )
import qualified GHC.Core.Type
  as GHC
    ( eqType, mkTyConApp, nonDetCmpType )
import qualified GHC.Core.Unify
  as GHC
    ( typesCantMatch )
import qualified GHC.Driver.Finder
  as GHC
    ( FindResult(..) )
import qualified GHC.Data.FastString
  as GHC
    ( fsLit )
import qualified GHC.Plugins
  as GHC
    ( Plugin(..), defaultPlugin, purePlugin )
import qualified GHC.Core.DataCon
  as GHC
    ( DataCon )
import qualified GHC.Core.TyCon
  as GHC
    ( TyCon(..) )
import qualified GHC.Tc.Plugin
  as GHC
    ( findImportedModule
    , lookupOrig, tcLookupTyCon, tcLookupDataCon
    , newGiven
    )
import qualified GHC.Tc.Types
  as GHC
    ( TcPlugin(..)
    , TcPluginM
    , TcPluginResult(..)
    )
import qualified GHC.Tc.Types.Constraint
  as GHC
    ( Ct(..), ctPred, ctLoc
    , bumpCtLocDepth, mkNonCanonical
    )
import qualified GHC.Tc.Types.Evidence
  as GHC
    ( EvTerm, Role(..) )
import qualified GHC.Types.Name.Occurrence
  as GHC
    ( mkDataOcc, mkTcOcc )
import qualified GHC.Types.Var
  as GHC
    ( TcTyVar, varUnique )
import qualified GHC.Utils.Outputable
  as GHC
    ( Outputable(..), pprTrace, text ) --, pprPanic )
import  GHC.Utils.Outputable
    ( (<+>) )

--------------------------------------------------------------------------------
-- Plugin definition and setup/finalisation.

plugin :: GHC.Plugin
plugin =
  GHC.defaultPlugin
    { GHC.tcPlugin        = tcPlugin
    , GHC.pluginRecompile = GHC.purePlugin
    }

tcPlugin :: [ String ] -> Maybe GHC.TcPlugin
tcPlugin _args =
  Just $
    GHC.TcPlugin
      { GHC.tcPluginInit  = tcPluginInit
      , GHC.tcPluginSolve = tcPluginSolve
      , GHC.tcPluginStop  = tcPluginStop
      }

data PluginDefs =
  PluginDefs
    { keyValTyCon       :: !GHC.TyCon
    , keyValDataCon     :: !GHC.DataCon
    , mapTyCon          :: !GHC.TyCon
    , fromListDataCon   :: !GHC.DataCon
    , lookupTyCon       :: !GHC.TyCon
    , insertTyCon       :: !GHC.TyCon
    , deleteTyCon       :: !GHC.TyCon
    , unionTyCon        :: !GHC.TyCon
    , differenceTyCon   :: !GHC.TyCon
    , doubleEqualsTyCon :: !GHC.TyCon
    }

findModule :: String -> String -> GHC.TcPluginM GHC.Module
findModule pkg modName = do
  findResult <- GHC.findImportedModule ( GHC.mkModuleName modName ) ( Just $ GHC.fsLit pkg )
  case findResult of
    GHC.Found _ res     -> pure res
    GHC.FoundMultiple _ -> error $ "MapPlugin: found multiple modules named " <> modName <> "."
    _                   -> error $ "MapPlugin: could not find any module named " <> modName <> "."

tcPluginInit :: GHC.TcPluginM PluginDefs
tcPluginInit = do
  dataTypeMapModule <- findModule "Map-Plugin" "Data.Type.Map"
  keyValTyCon       <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule      ( GHC.mkTcOcc   ":->"        )
  keyValDataCon     <- GHC.tcLookupDataCon =<< GHC.lookupOrig dataTypeMapModule      ( GHC.mkDataOcc ":->"        )
  mapTyCon          <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule      ( GHC.mkTcOcc   "Map"        )
  fromListDataCon   <- GHC.tcLookupDataCon =<< GHC.lookupOrig dataTypeMapModule      ( GHC.mkDataOcc "FromList"   )
  lookupTyCon       <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule      ( GHC.mkTcOcc   "Lookup"     )
  insertTyCon       <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule      ( GHC.mkTcOcc   "Insert"     )
  deleteTyCon       <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule      ( GHC.mkTcOcc   "Delete"     )
  unionTyCon        <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule      ( GHC.mkTcOcc   "Union"      )
  differenceTyCon   <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule      ( GHC.mkTcOcc   "Difference" )
  dataTypeEqualityModule <- findModule "base" "Data.Type.Equality"
  doubleEqualsTyCon <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeEqualityModule ( GHC.mkTcOcc   "=="         )
  pure ( PluginDefs { .. } )

tcPluginStop :: PluginDefs -> GHC.TcPluginM ()
tcPluginStop _ = pure ()

--------------------------------------------------------------------------------
-- Looking through types and given constraints,
-- in order to find types we're interested in.

-- Horrible instances so that we can conveniently use sets and maps.
instance Eq  GHC.Ct where
  ct1 == ct2 = compare ct1 ct2 == EQ
instance Ord GHC.Ct where
  compare ct1 ct2 =
    case compare ( I# ( dataToTag# ct1 ) ) ( I# ( dataToTag# ct2 ) ) of
      EQ   -> compare ( GHC.ctPred ct1 ) ( GHC.ctPred ct2 )
      uneq -> uneq
instance Eq  GHC.Type where
  ty1 == ty2 = compare ty1 ty2 == EQ
instance Ord GHC.Type where
  compare = GHC.nonDetCmpType

data TyConApp
  = TyEqRHS !GHC.Type -- RHS of a CTyEqCan.
  | Eq      !GHC.Type !GHC.Type !GHC.Type -- ^ 'Data.Type.Equality.=='
  | Boolean !Bool
  | Maybe   !GHC.Type !( Maybe GHC.Type )
  | Lookup  !GHC.Type !GHC.Type !GHC.Type !GHC.Type
  | Insert  !GHC.Type !GHC.Type !GHC.Type !GHC.Type !GHC.Type
  | Delete  !GHC.Type !GHC.Type !GHC.Type !GHC.Type
  -- others: todo
  deriving stock ( Eq, Ord )

instance GHC.Outputable TyConApp where
  ppr ( TyEqRHS t           ) = GHC.text "TyEqRhs"        <+> GHC.ppr t
  ppr ( Eq      k a b       ) = GHC.text "Eq "            <+> GHC.ppr [ k, a, b ]
  ppr ( Boolean b           ) = GHC.text "Boolean"        <+> GHC.ppr b
  ppr ( Maybe   k ( Just v )) = GHC.text "Maybe: Just"    <+> GHC.ppr [ k, v ]
  ppr ( Maybe   k Nothing   ) = GHC.text "Maybe: Nothing" <+> GHC.ppr [ k ]
  ppr ( Lookup  kk kv k m   ) = GHC.text "Lookup"         <+> GHC.ppr [ kk, kv, k, m]
  ppr ( Insert  kk kv k v m ) = GHC.text "Insert"         <+> GHC.ppr [ kk, kv, k, v, m ]
  ppr ( Delete  kk kv k m   ) = GHC.text "Delete"         <+> GHC.ppr [ kk, kv, k, m ]

-- | Recognise fully saturated applications of supported types,
-- such as @ Insert {kind_k} {kind_v} k v m @.
recogniseExplicitTyConApp :: PluginDefs -> GHC.TyCon -> [ GHC.Type ] -> Maybe TyConApp
recogniseExplicitTyConApp ( PluginDefs { .. } ) tyCon args
  | tyCon == doubleEqualsTyCon
  , [ kind, a, b ] <- args
  = Just $ Eq kind a b
  | tyCon == GHC.promotedTrueDataCon
  = Just ( Boolean True )
  | tyCon == GHC.promotedFalseDataCon
  = Just ( Boolean False )
  | tyCon == GHC.promotedNothingDataCon
  , [ kind ] <- args
  = Just ( Maybe kind Nothing )
  | tyCon == GHC.promotedJustDataCon
  , [ kind, v ] <- args
  = Just ( Maybe kind ( Just v ) )
  | tyCon == lookupTyCon
  , [ kind_k, kind_v, k, m ] <- args
  = Just $ Lookup kind_k kind_v k m
  | tyCon == insertTyCon
  , [ kind_k, kind_v, k, v, m ] <- args
  = Just $ Insert kind_k kind_v k v m
  | tyCon == deleteTyCon
  , [ kind_k, kind_v, k, m ] <- args
  = Just $ Delete kind_k kind_v k m
  | otherwise
  = Nothing

-- | Recognise supported type family applications and equalities in the provided list of given constraints.
recogniseGivenTyConApps :: PluginDefs -> [ GHC.Ct ] -> Map GHC.TcTyVar ( Set TyConApp )
recogniseGivenTyConApps pluginDefs = Map.fromListWith Set.union . mapMaybe \case
  GHC.CFunEqCan { cc_fun, cc_tyargs, cc_fsk }
    -> ( cc_fsk, ) . Set.singleton <$> recogniseExplicitTyConApp pluginDefs cc_fun cc_tyargs
  GHC.CTyEqCan { cc_tyvar, cc_rhs }
    -> Just ( cc_tyvar, Set.singleton ( TyEqRHS cc_rhs ) )
  _ -> Nothing

-- | Recognise supported types:
--
--  - type is explicitly a recognised @ TyConApp @,
--  - type is a flattening type variable associated to a recognised @ CFunEqCan @,
--  - type is transitively equal to a supported type,
--    through an explicit @ CTyEqCan @: @ ty ~# recognisedTyConApp @.
recogniseTyConApps :: PluginDefs -> [ GHC.Ct ] -> Map GHC.TcTyVar ( Set TyConApp )
recogniseTyConApps pluginDefs givens = transitiveClosure 0 basicApps
  where
    basicApps :: Map GHC.TcTyVar ( Set TyConApp )
    basicApps = recogniseGivenTyConApps pluginDefs givens
    transitiveClosure :: Int -> Map GHC.TcTyVar ( Set TyConApp ) -> Map GHC.TcTyVar ( Set TyConApp )
    transitiveClosure iter apps
      | iter > 100
      = apps
      | otherwise
      = let
          newTransitiveApps :: Map GHC.TcTyVar ( Set TyConApp )
          newTransitiveApps = ( `Map.mapMaybeWithKey` apps ) \ tv tv_apps ->
            ( `foldMap` tv_apps ) \case
              -- Found a @ CTyEqCan @ : @ ty ~# rhs @.
              -- Go through the map of TyConApps to see if @ rhs @ has any,
              -- to transitively add them to @ ty @.
              TyEqRHS rhs ->
                let
                  newApps :: Set TyConApp
                  newApps = ( `Map.foldMapWithKey` apps ) \ tv' tyConApps ->
                    if   ( GHC.TyVarTy tv' ) `GHC.eqType` rhs
                    then tyConApps
                    else Set.empty
                in
                  case Map.lookup tv apps of
                    -- No TyConApps for @ tv @ (neither before nor after).
                    Nothing
                      | null newApps
                      -> Nothing
                    -- No new TyConApps for @ tv @.
                    Just prevApps
                      | newApps `Set.isSubsetOf` prevApps
                      -> Nothing
                    -- New TyConApps for @ tv @.
                    _ -> Just newApps
              _ -> Nothing
        in
          if null newTransitiveApps
          then apps
          else transitiveClosure ( iter + 1 ) ( Map.unionWith Set.union apps newTransitiveApps )

recognise :: PluginDefs -> Map GHC.TcTyVar ( Set TyConApp ) -> GHC.Type -> Set TyConApp
recognise pluginDefs tyConApps ty = case ty of
  GHC.TyConApp tyCon args
    | Just app <- recogniseExplicitTyConApp pluginDefs tyCon args
    -> Set.singleton app
  GHC.TyVarTy tv
    -> Map.foldMapWithKey ( lookupTv tv ) tyConApps
  _ -> Set.empty
  where
    lookupTv :: GHC.TcTyVar -> GHC.TcTyVar -> Set TyConApp -> Set TyConApp
    lookupTv tv tv' apps
      | GHC.varUnique tv == GHC.varUnique tv'
      = apps
      | any ( \case { TyEqRHS ( GHC.TyVarTy tv'' ) | GHC.varUnique tv == GHC.varUnique tv'' -> True; _ -> False } ) apps
      = Set.insert ( TyEqRHS ( GHC.TyVarTy tv' ) ) apps
      | otherwise
      = Set.empty

--------------------------------------------------------------------------------
-- Simplification of type family applications.

-- | Try to simplify a type, e.g. simplify @ Lookup k ( Insert k v s ) @ to @ v @.
simplify :: PluginDefs -> [ GHC.Ct ] -> Map GHC.TcTyVar ( Set TyConApp ) -> GHC.Ct -> GHC.Type -> GHC.TcPluginM [ GHC.Ct ]
simplify pluginDefs _givens tyConApps wanted ty =
  coerce $ toList <$> ( `foldMap` ty_apps ) \case
      Lookup kind_k kind_v k kvs -> Ap $ do
        let
          simpls :: Set GHC.Type
          simpls =
            Set.map
              ( lookupSimplificationTy pluginDefs kind_k kind_v k )
              ( simplifyLookup pluginDefs tyConApps k kvs )
        Set.fromList
          <$>
            traverse
              ( newDeducedGivenEq wanted ty )
              ( toList simpls )
      _ -> pure Set.empty
  where
    ty_apps :: Set TyConApp
    ty_apps = recognise pluginDefs tyConApps ty

-- | Outcome of attempting to simplify a type family application `F ... a`.
data TyFamAppSimplification arg res
  = SimplifyArg arg -- ^ Simplification of the last type family argument.
  | Result      res -- ^ Computation of the full type family application.
  deriving stock ( Eq, Ord )

-- | Tries to simplify a type family application @ Lookup k kvs @.
simplifyLookup :: PluginDefs -> Map GHC.TcTyVar ( Set TyConApp ) -> GHC.Type -> GHC.Type
               -> Set ( TyFamAppSimplification GHC.Type ( Maybe GHC.Type ) )
simplifyLookup pluginDefs tyConApps k0 kvs0 =
    ( `foldMap` ( recognise pluginDefs tyConApps kvs0 ) ) \case
      Insert _kind_k _kind_v k1 v1 kvs1 ->
        let
          mbEq :: Maybe Bool
          mbEq = eqTy pluginDefs tyConApps k0 k1
        in
          case mbEq of
            -- @ Lookup k0 ( Insert k1 v1 kvs1 ) ~ Just v1 @ when @ k0 ~ k1 @.
            Just True  -> Set.singleton ( Result $ Just v1 )
            -- @ Lookup k0 ( Insert k1 v1 kvs1 ) ~ Lookup k0 kvs1 @ when @ k0 /~ k1 @.
            Just False -> Set.singleton ( SimplifyArg kvs1 )
            Nothing    -> Set.empty
      Delete _kind_k _kind_v k1 kvs1 ->
        let
          mbEq :: Maybe Bool
          mbEq = eqTy pluginDefs tyConApps k0 k1
        in
          case mbEq of
            -- @ Lookup k0 ( Delete k1 kvs1 ) ~ Nothing @ when @ k0 ~ k1 @.
            Just True  -> Set.singleton ( Result Nothing )
            -- @ Lookup k0 ( Delete k1 kvs1 ) ~ Lookup k0 kvs1 @ when @ k0 /~ k1 @.
            Just False -> Set.singleton ( SimplifyArg kvs1 )
            -- If we don't know whether @ k0 @ and @ k1 @ can unify,
            -- it is still worth trying to simplify @ kvs1 @, as @ Lookup k0 kvs1 ~ Nothing @
            -- would also imply that @ Lookup k0 ( Delete k1 kvs1 ) ~ Nothing @.
            Nothing ->
              let
                simplFurther :: Set ( TyFamAppSimplification GHC.Type ( Maybe GHC.Type ) )
                simplFurther = simplifyLookup pluginDefs tyConApps k0 kvs1
              in
                if any ( \case { Result Nothing -> True; _ -> False } ) simplFurther
                then Set.singleton ( Result Nothing )
                else Set.empty
      _ -> Set.empty

-- | Returns the type corresponding to the outcome of simplifying
-- an expression of the form @ Lookup k m @.
lookupSimplificationTy :: PluginDefs -> GHC.Type -> GHC.Type -> GHC.Type
                       -> TyFamAppSimplification GHC.Type ( Maybe GHC.Type )
                       -> GHC.Type
lookupSimplificationTy ( PluginDefs { lookupTyCon } ) kind_k kind_v k simpl = case simpl of
  SimplifyArg arg     -> GHC.mkTyConApp lookupTyCon [ kind_k, kind_v, k, arg ]
  Result ( Just res ) -> GHC.mkTyConApp GHC.promotedJustDataCon [ kind_v, res ]
  Result Nothing      -> GHC.mkTyConApp GHC.promotedNothingDataCon [ kind_v ]

--------------------------------------------------------------------------------
-- Handling equalities.

-- | Returns a new given equality constraint @ lhs ~ rhs @,
-- obtained by bumping the depth of the provided constraint.
newDeducedGivenEq :: GHC.Ct -> GHC.Type -> GHC.Type -> GHC.TcPluginM GHC.Ct
newDeducedGivenEq ct lhs rhs = do
  let
    coercion :: GHC.Coercion
    coercion = GHC.mkUnivCo ( GHC.PluginProv "Map-Plugin") GHC.Nominal lhs rhs
  evidence <-
    GHC.newGiven
      ( GHC.bumpCtLocDepth $ GHC.ctLoc ct )
      ( GHC.mkPrimEqPredRole GHC.Nominal lhs rhs )
      ( GHC.Coercion coercion )
  pure ( GHC.mkNonCanonical evidence )

-- | Computes whether `lhs == rhs`.
--
--  - @ Just True @: types are equal,
--  - @ Just False @: types are apart,
--  - @ Nothing @: unknown at this stage.
eqTy :: PluginDefs -> Map GHC.TcTyVar ( Set TyConApp ) -> GHC.Type -> GHC.Type -> Maybe Bool
eqTy pluginDefs tyConApps lhs rhs
  | GHC.eqType lhs rhs
  = Just True
  | Just True <- givenEq
  = Just True
  | GHC.typesCantMatch [ ( lhs, rhs ) ]
  = Just False
  | Just False <- givenEq
  = Just False
  | otherwise
  = Nothing
  where
    givenEq :: Maybe Bool
    givenEq = lookupGivenEq pluginDefs tyConApps lhs rhs

-- | Try to compute @ lhs == rhs @ using information deduced from given constraints.
lookupGivenEq :: PluginDefs -> Map GHC.TcTyVar ( Set TyConApp ) -> GHC.Type -> GHC.Type -> Maybe Bool
lookupGivenEq pluginDefs tyConApps lhs rhs = coerce $ Map.foldMapWithKey ( \ tv -> foldMap ( findGivenEq tv ) ) tyConApps
  where
    -- | Look for type family applications "lhs == rhs"
    findGivenEq :: GHC.TcTyVar -> TyConApp -> Maybe ( First Bool )
    findGivenEq tv ( Eq _ a b )
      | Just True <- eqTy pluginDefs tyConApps lhs a
      , Just True <- eqTy pluginDefs tyConApps rhs b
      = findValue tv
      | Just True <- eqTy pluginDefs tyConApps rhs a
      , Just True <- eqTy pluginDefs tyConApps lhs b
      = findValue tv
    findGivenEq _ _
      = Nothing
    findValue :: GHC.TcTyVar -> Maybe ( First Bool )
    findValue tv = foldMap boolValue ( recognise pluginDefs tyConApps ( GHC.TyVarTy tv ) )
    boolValue :: TyConApp -> Maybe ( First Bool )
    boolValue ( Boolean b ) = Just ( First b )
    boolValue _             = Nothing

--------------------------------------------------------------------------------
-- Solver part of the plugin.

tcPluginSolve :: PluginDefs -> [ GHC.Ct ] -> [ GHC.Ct ] -> [ GHC.Ct ] -> GHC.TcPluginM GHC.TcPluginResult
tcPluginSolve _defs _givens _deriveds []      = pure $ GHC.TcPluginOk [] []
tcPluginSolve  defs  givens  deriveds wanteds = do
  let
    tyConApps :: Map GHC.TcTyVar ( Set TyConApp )
    tyConApps
      = GHC.pprTrace "Givens:"   ( GHC.ppr givens   )
      . GHC.pprTrace "Deriveds:" ( GHC.ppr deriveds )
      . GHC.pprTrace "Wanteds:"  ( GHC.ppr wanteds  )
      $ recogniseTyConApps defs givens
  ( contras, oks )
    <- GHC.pprTrace "TyConApps:" ( GHC.ppr tyConApps )
     $ partitionEithers
    <$> traverse ( \ wanted -> specifyWanted wanted <$> solveWanted defs givens tyConApps deriveds wanted ) wanteds
  case contras of
    [] ->
      let
        solveds :: [ ( GHC.EvTerm, GHC.Ct ) ]
        news    :: [ GHC.Ct ]
        ( solveds, news ) = ( catMaybes *** join ) ( unzip oks )
      in  pure $ GHC.TcPluginOk
                  ( GHC.pprTrace "Solveds:" ( GHC.ppr solveds ) $ solveds )
                  ( GHC.pprTrace "News:"    ( GHC.ppr news    ) $ news    )
    _  -> pure $ GHC.TcPluginContradiction
                  ( GHC.pprTrace "Contras:" ( GHC.ppr contras ) $ contras )

-- | Outcome of running the Map plugin on a single wanted constraint.
data SolverResult
  = Unsolved -- ^ Wanted constraint was not solved, but new constraints might be emitted.
    { newCts   :: ![ GHC.Ct ] }
  | Solved   -- ^ Wanted constraint has been solved: evidence, and new constraints to emit.
    { evidence :: !GHC.EvTerm
    , newCts   :: ![ GHC.Ct ]
    }
  | Contradiction -- ^ The plugin has uncovered a contradiction.

pattern Ignore :: SolverResult
pattern Ignore = Unsolved []

-- | Try to solve a wanted constraint.
--
-- This function currently never directly solves the constraint,
-- but might make progress (emitting new given constraints),
-- which hopefully will allow GHC to solve it.
solveWanted :: PluginDefs -> [ GHC.Ct ] -> Map GHC.TcTyVar ( Set TyConApp ) -> [ GHC.Ct ] -> GHC.Ct -> GHC.TcPluginM SolverResult
solveWanted pluginDefs givens tyConApps _deriveds wanted =
  case GHC.classifyPredType ( GHC.ctPred wanted ) of
    GHC.EqPred GHC.NomEq lhs rhs -> do
      newCts <- concat <$> traverse ( simplify pluginDefs givens tyConApps wanted ) [ lhs, rhs ]
      pure $ Unsolved {..}
    _ -> pure Ignore

-- | Passthrough of the wanted constraint, to report a solution/contradiction.
specifyWanted :: GHC.Ct -> SolverResult -> Either GHC.Ct ( Maybe ( GHC.EvTerm, GHC.Ct ), [ GHC.Ct ] )
specifyWanted _      ( Unsolved {..} ) = Right ( Nothing, newCts )
specifyWanted wanted ( Solved   {..} ) = Right ( Just ( evidence, wanted ), newCts )
specifyWanted wanted Contradiction     = Left wanted
