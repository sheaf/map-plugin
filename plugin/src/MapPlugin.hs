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
    ( (***), first )
import Control.Monad
    ( guard, join )
import Data.Coerce
    ( coerce )
import Data.Either
    ( partitionEithers )
import Data.Foldable
    ( toList )
import Data.Maybe
    ( catMaybes, mapMaybe )
import Data.Monoid
    ( Any(..), Ap(..) )

-- containers
import Data.Set
    ( Set )
import qualified Data.Set
  as Set
    ( empty, fromList, insert
    , map, singleton
    )

-- data-partition
import Data.Partition as Partition
  ( fromSets, nontrivialSets )

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
import qualified GHC.Core.DataCon
  as GHC
    ( DataCon )
import qualified GHC.Core.Predicate
  as GHC
    ( Pred(..), classifyPredType
    , EqRel(..)
    )
import qualified GHC.Core.TyCo.Rep
  as GHC
    ( Type(..), Kind
    , UnivCoProvenance(..)
    )
import qualified GHC.Core.TyCon
  as GHC
    ( TyCon(..) )
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
    ( TcTyVar )
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

-- Unfortunate instances so that we can conveniently use sets and maps.
instance Eq  GHC.Type where
  ty1 == ty2 = compare ty1 ty2 == EQ
instance Ord GHC.Type where
  compare = GHC.nonDetCmpType

data TyConApp
  = Eq      !GHC.Kind !GHC.Type !GHC.Type -- ^ 'Data.Type.Equality.=='
  | Boolean !Bool
  | Maybe   !GHC.Kind !( Maybe GHC.Type )
  | Lookup  !GHC.Kind !GHC.Kind !GHC.Type !GHC.Type
  | Insert  !GHC.Kind !GHC.Kind !GHC.Type !GHC.Type !GHC.Type
  | Delete  !GHC.Kind !GHC.Kind !GHC.Type !GHC.Type
  -- others: todo
  deriving stock ( Eq, Ord )

instance GHC.Outputable TyConApp where
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
recogniseGivenTyConApps :: PluginDefs -> [ GHC.Ct ] -> ( [ ( GHC.Type, GHC.Type ) ], [ ( GHC.TcTyVar, TyConApp ) ] )
recogniseGivenTyConApps pluginDefs = partitionEithers . mapMaybe \case
  GHC.CFunEqCan { cc_fun, cc_tyargs, cc_fsk }
    -> Right . ( cc_fsk, ) <$> recogniseExplicitTyConApp pluginDefs cc_fun cc_tyargs
  GHC.CTyEqCan { cc_tyvar, cc_rhs }
    -> Just $ Left ( GHC.TyVarTy cc_tyvar, cc_rhs )
  _ -> Nothing

-- | Recognise supported types:
--
--  - type is explicitly a recognised @ TyConApp @,
--  - type is a flattening type variable associated to a recognised @ CFunEqCan @,
--  - type is transitively equal to a supported type,
--    through an explicit @ CTyEqCan @: @ ty ~# recognisedTyConApp @.
recogniseTyConApps :: PluginDefs -> [ GHC.Ct ] -> [ ( Set GHC.Type, Set TyConApp ) ]
recogniseTyConApps pluginDefs givens =
  ( `mapMaybe` comps ) \ comp_tys ->
    let
      comp_apps :: Set TyConApp
      comp_apps = foldMap tyConApps comp_tys
    in
      if   null comp_apps
      then Nothing
      else Just ( comp_tys, comp_apps )

  where
    comps     :: [ Set GHC.Type ]
    basicApps :: [ ( GHC.TcTyVar, TyConApp ) ]
    ( comps, basicApps ) = first sccs $ recogniseGivenTyConApps pluginDefs givens

    tyConApps :: GHC.Type -> Set TyConApp
    tyConApps ty =
      let
        apps :: Set TyConApp
        apps
          | Just explicitApp <- mbExplicitApp
          = Set.insert explicitApp lookedUpApps
          | otherwise
          = lookedUpApps
        mbExplicitApp :: Maybe TyConApp
        mbExplicitApp = case ty of
          GHC.TyConApp tyCon args
            -> recogniseExplicitTyConApp pluginDefs tyCon args
          _ -> Nothing
        lookedUpApps :: Set TyConApp
        lookedUpApps = Set.fromList $ ( `mapMaybe` basicApps ) \ ( tv, app ) -> do
          guard ( GHC.eqType ty ( GHC.TyVarTy tv ) )
          pure app
      in
        apps


sccs :: Ord a => [ ( a, a ) ] -> [ Set a ]
sccs = Partition.nontrivialSets
     . Partition.fromSets
     . map ( \ ( x, y ) -> Set.fromList [x,y] )

recognise :: PluginDefs -> [ ( Set GHC.Type, Set TyConApp ) ] -> GHC.Type -> Set TyConApp
recognise pluginDefs tyConApps ty
  | GHC.TyConApp tyCon args <- ty
  , Just app <- recogniseExplicitTyConApp pluginDefs tyCon args
  = Set.insert app ( go tyConApps )
  | otherwise
  = go tyConApps
  where
    go :: [ ( Set GHC.Type, Set TyConApp ) ] -> Set TyConApp
    go [] = Set.empty
    go ( ( comp, apps ) : comps )
      | any ( GHC.eqType ty ) comp
      = apps
      | otherwise
      = go comps

--------------------------------------------------------------------------------
-- Simplification of type family applications.

-- | Try to simplify a type, e.g. simplify @ Lookup k ( Insert k v s ) @ to @ v @.
simplify :: PluginDefs -> [ GHC.Ct ] -> [ ( Set GHC.Type, Set TyConApp ) ] -> GHC.Ct -> GHC.Type -> GHC.TcPluginM [ GHC.Ct ]
simplify pluginDefs _givens tyConApps wanted ty =
  coerce $ ( `foldMap` ty_apps ) \case
      Lookup kind_k kind_v k kvs -> Ap $ do
        let
          simpls :: Set GHC.Type
          simpls =
            Set.map
              ( lookupSimplificationTy pluginDefs kind_k kind_v k )
              ( simplifyLookup pluginDefs tyConApps k kvs )
        traverse
          ( newDeducedGivenEq wanted ty )
          ( toList simpls )
      _ -> pure []
  where
    ty_apps :: Set TyConApp
    ty_apps = recognise pluginDefs tyConApps ty

-- | Outcome of attempting to simplify a type family application `F ... a`.
data TyFamAppSimplification arg res
  = SimplifyArg arg -- ^ Simplification of the last type family argument.
  | Result      res -- ^ Computation of the full type family application.
  deriving stock ( Eq, Ord )

-- | Tries to simplify a type family application @ Lookup k kvs @.
simplifyLookup :: PluginDefs -> [ ( Set GHC.Type, Set TyConApp ) ] -> GHC.Type -> GHC.Type
               -> Set ( TyFamAppSimplification GHC.Type ( Maybe GHC.Type ) )
simplifyLookup pluginDefs tyConApps k0 kvs0 =
    ( `foldMap` ( recognise pluginDefs tyConApps kvs0 ) ) \case
      Insert _kind_k _kind_v k1 v1 kvs1 ->
        let
          mbEq :: Maybe Bool
          mbEq = eqTy tyConApps k0 k1
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
          mbEq = eqTy tyConApps k0 k1
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
lookupSimplificationTy :: PluginDefs -> GHC.Kind -> GHC.Kind -> GHC.Type
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
eqTy :: [ ( Set GHC.Type, Set TyConApp ) ] -> GHC.Type -> GHC.Type -> Maybe Bool
eqTy tyConApps lhs rhs
  | GHC.eqType lhs rhs
  = Just True
  | lookupGivenEq tyConApps lhs rhs
  = Just True
  | GHC.typesCantMatch [ ( lhs, rhs ) ]
  = Just False
  | lookupGivenUnEq tyConApps lhs rhs
  = Just False
  | otherwise
  = Nothing

-- | Compute whether given constraints imply that @ lhs ~ rhs @.
lookupGivenEq :: [ ( Set GHC.Type, Set TyConApp ) ] -> GHC.Type -> GHC.Type -> Bool
lookupGivenEq tyConApps lhs rhs = any eqEvidence tyConApps
  where
    -- Check whether @ lhs @ and @ rhs @ appear in the same component.
    eqEvidence :: ( Set GHC.Type, Set TyConApp ) -> Bool
    eqEvidence ( tys, _ ) = case foldMap elems tys of
      ( Any True, Any True ) -> True
      _                      -> False

    elems :: GHC.Type -> ( Any, Any )
    elems ty = ( Any $ GHC.eqType ty lhs, Any $ GHC.eqType ty rhs )

-- | Compute whether given constraints imply that @ ( lhs == rhs ) ~ False $.
lookupGivenUnEq :: [ ( Set GHC.Type, Set TyConApp ) ] -> GHC.Type -> GHC.Type -> Bool
lookupGivenUnEq tyConApps lhs rhs = any uneqEvidence tyConApps
  where
    -- Check whether there exists a component that contains both:
    --
    --  - an equality @ x == y @, with either @ x ~ lhs @ and @ y ~ rhs @ or @ x ~ rhs @ and @ y ~ lhs @.
    --  - the constant @ False @.
    uneqEvidence :: ( Set GHC.Type, Set TyConApp ) -> Bool
    uneqEvidence ( tys, apps ) =
      any
          ( \case
              Eq _ x y
                |   ( GHC.eqType x lhs || lookupGivenEq tyConApps x lhs ) && ( GHC.eqType y rhs || lookupGivenEq tyConApps y rhs )
                ||  ( GHC.eqType x rhs || lookupGivenEq tyConApps x rhs ) && ( GHC.eqType y lhs || lookupGivenEq tyConApps y lhs )
                -> True
              _ -> False
          )
          apps
      &&
      ( any
          ( \case
              GHC.TyConApp tyCon []
                | tyCon == GHC.promotedFalseDataCon
                -> True
              _ -> False
          )
          tys
      || any ( \case { Boolean False -> True; _ -> False } ) apps
      )

--------------------------------------------------------------------------------
-- Solver part of the plugin.

tcPluginSolve :: PluginDefs -> [ GHC.Ct ] -> [ GHC.Ct ] -> [ GHC.Ct ] -> GHC.TcPluginM GHC.TcPluginResult
tcPluginSolve _defs _givens _deriveds []      = pure $ GHC.TcPluginOk [] []
tcPluginSolve  defs  givens  deriveds wanteds = do
  let
    tyConApps :: [ ( Set GHC.Type, Set TyConApp ) ]
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
solveWanted :: PluginDefs -> [ GHC.Ct ] -> [ ( Set GHC.Type, Set TyConApp ) ] -> [ GHC.Ct ] -> GHC.Ct -> GHC.TcPluginM SolverResult
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
